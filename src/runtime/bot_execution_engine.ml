(*
 * Bot Execution Engine - Actually runs the bots
 * 
 * This bridges the formally verified NVS network with real bot processes
 *)

open Unix
open Lwt.Syntax

(* ========== Bot Process Management ========== *)

module BotProcess = struct
  
  type bot_executable =
    | CoqGymBot of string        (* Path to CoqGym model *)
    | ProverBot of string        (* Path to ProverBot executable *)
    | TacticToeBot of string     (* Path to TacticToe *)
    | CoqHammerBot               (* Uses system coqhammer *)
    | CustomBot of string        (* Custom executable path *)
  
  type bot_instance = {
    pid: int;
    executable: bot_executable;
    nvs_name: string;
    stdin_fd: Unix.file_descr;
    stdout_fd: Unix.file_descr;
    stderr_fd: Unix.file_descr;
    mutable status: [`Running | `Stopped | `Failed of string];
    inbox_addr: int64;           (* NVS address for IPC *)
    heartbeat_time: float ref;
  }
  
  (* Spawn a bot process *)
  let spawn_bot ~executable ~nvs_name ~inbox_addr =
    let (cmd, args) = match executable with
    | CoqGymBot model_path ->
        ("python3", [|"python3"; "-m"; "coqgym.predict"; "--model"; model_path|])
    | ProverBot path ->
        (path, [|path; "--interactive"|])
    | TacticToeBot path ->
        (path, [|path; "--socket-mode"|])
    | CoqHammerBot ->
        ("coqtop", [|"coqtop"; "-I"; "+coqhammer"|])
    | CustomBot path ->
        (path, [|path|])
    in
    
    let (stdin_read, stdin_write) = Unix.pipe () in
    let (stdout_read, stdout_write) = Unix.pipe () in
    let (stderr_read, stderr_write) = Unix.pipe () in
    
    Printf.printf "[Runtime] Spawning bot: %s -> %s\n" nvs_name cmd;
    
    let pid = Unix.create_process cmd args stdin_read stdout_write stderr_write in
    
    (* Close child-side fds in parent *)
    Unix.close stdin_read;
    Unix.close stdout_write;
    Unix.close stderr_write;
    
    {
      pid;
      executable;
      nvs_name;
      stdin_fd = stdin_write;
      stdout_fd = stdout_read;
      stderr_fd = stderr_read;
      status = `Running;
      inbox_addr;
      heartbeat_time = ref (Unix.gettimeofday ());
    }
  
  (* Send command to bot process *)
  let send_command bot command =
    try
      let cmd_bytes = Bytes.of_string (command ^ "\n") in
      let written = Unix.write bot.stdin_fd cmd_bytes 0 (Bytes.length cmd_bytes) in
      if written = Bytes.length cmd_bytes then
        Ok ()
      else
        Error "Partial write to bot process"
    with
    | Unix.Unix_error (err, _, _) ->
        bot.status <- `Failed (Unix.error_message err);
        Error ("Bot communication failed: " ^ Unix.error_message err)
  
  (* Read response from bot *)
  let read_response bot ~timeout =
    try
      (* Set timeout *)
      let old_alarm = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> ())) in
      let _ = Unix.alarm (int_of_float timeout) in
      
      let buffer = Bytes.create 4096 in
      let bytes_read = Unix.read bot.stdout_fd buffer 0 4096 in
      let _ = Unix.alarm 0 in
      Sys.set_signal Sys.sigalrm old_alarm;
      
      if bytes_read > 0 then
        Ok (Bytes.sub_string buffer 0 bytes_read)
      else
        Error "No response from bot"
    with
    | Unix.Unix_error (EAGAIN, _, _) -> Error "Bot response timeout"
    | Unix.Unix_error (err, _, _) ->
        bot.status <- `Failed (Unix.error_message err);
        Error ("Bot read failed: " ^ Unix.error_message err)
  
  (* Kill bot process *)
  let kill_bot bot =
    Printf.printf "[Runtime] Killing bot: %s (pid: %d)\n" bot.nvs_name bot.pid;
    (try Unix.kill bot.pid Sys.sigterm with _ -> ());
    Unix.close bot.stdin_fd;
    Unix.close bot.stdout_fd;
    Unix.close bot.stderr_fd;
    bot.status <- `Stopped
end

(* ========== Bot Runtime Manager ========== *)

module BotRuntime = struct
  
  type runtime = {
    registry: BotNVS.registry;           (* From formal verification *)
    active_bots: (string, BotProcess.bot_instance) Hashtbl.t;
    shared_memory: Nvs_bot_network.BotInbox.inbox Hashtbl.t;
    mutable should_stop: bool;
  }
  
  let create_runtime registry_size =
    let registry = BotNVS.create_registry registry_size in
    {
      registry;
      active_bots = Hashtbl.create 64;
      shared_memory = Hashtbl.create 64;
      should_stop = false;
    }
  
  (* Start a bot and register it in NVS *)
  let start_bot runtime ~name ~executable ~capabilities =
    Printf.printf "[Runtime] Starting bot: %s\n" name;
    
    (* Register in NVS (formally verified) *)
    let nvs_entry = BotNVS.register_bot runtime.registry ~name ~capabilities in
    
    (* Create shared memory inbox *)
    let inbox = BotInbox.create 
                  runtime.registry.memory
                  nvs_entry.shm_offset
                  nvs_entry.inbox_size in
    
    Hashtbl.add runtime.shared_memory name inbox;
    
    (* Spawn actual process *)
    let bot_instance = BotProcess.spawn_bot 
                        ~executable 
                        ~nvs_name:name 
                        ~inbox_addr:nvs_entry.address in
    
    Hashtbl.add runtime.active_bots name bot_instance;
    
    Printf.printf "[Runtime] Bot %s started at address 0x%Lx\n" 
      name nvs_entry.address;
    
    Ok nvs_entry
  
  (* Process messages from shared memory to bot processes *)
  let process_bot_messages runtime bot_name =
    match Hashtbl.find_opt runtime.shared_memory bot_name,
          Hashtbl.find_opt runtime.active_bots bot_name with
    | Some inbox, Some bot ->
        (* Check for packets in shared memory *)
        (match BotInbox.receive_packet inbox with
         | Some packet ->
             let goal = Bytes.to_string packet.payload in
             Printf.printf "[Runtime] Sending to %s: %s\n" bot_name goal;
             
             (* Send to actual bot process *)
             (match BotProcess.send_command bot goal with
              | Ok () ->
                  (* Read bot response *)
                  (match BotProcess.read_response bot ~timeout:5.0 with
                   | Ok response ->
                       Printf.printf "[Runtime] Bot %s responded: %s\n" 
                         bot_name response;
                       
                       (* Send response back via shared memory *)
                       let response_packet = {
                         packet with
                         header = { packet.header with packet_type = 0x02 };
                         payload = Bytes.of_string response;
                       } in
                       
                       (* Find sender's inbox and send response *)
                       (* This would use the formally verified send mechanisms *)
                       Ok response
                   | Error err ->
                       Printf.printf "[Runtime] Bot %s failed to respond: %s\n"
                         bot_name err;
                       Error err)
              | Error err ->
                  Printf.printf "[Runtime] Failed to send to bot %s: %s\n"
                    bot_name err;
                  Error err)
         | None -> Ok ""  (* No messages *)
        )
    | _ -> Error ("Bot not found: " ^ bot_name)
  
  (* Main runtime loop *)
  let run_runtime runtime =
    Printf.printf "[Runtime] Starting bot runtime engine\n";
    
    while not runtime.should_stop do
      (* Process messages for all active bots *)
      Hashtbl.iter (fun bot_name _ ->
        match process_bot_messages runtime bot_name with
        | Ok _ -> ()
        | Error err -> Printf.printf "[Runtime] Error: %s\n" err
      ) runtime.active_bots;
      
      (* Check for dead bots *)
      let dead_bots = ref [] in
      Hashtbl.iter (fun name bot ->
        (try
           let (_, status) = Unix.waitpid [Unix.WNOHANG] bot.pid in
           if status <> Unix.WEXITED 0 then begin
             Printf.printf "[Runtime] Bot %s died\n" name;
             dead_bots := name :: !dead_bots
           end
         with Unix.Unix_error (Unix.ECHILD, _, _) -> 
           dead_bots := name :: !dead_bots)
      ) runtime.active_bots;
      
      (* Clean up dead bots *)
      List.iter (fun name ->
        match Hashtbl.find_opt runtime.active_bots name with
        | Some bot ->
            BotProcess.kill_bot bot;
            Hashtbl.remove runtime.active_bots name;
            Hashtbl.remove runtime.shared_memory name;
            BotNVS.update_status runtime.registry name `Dead
        | None -> ()
      ) !dead_bots;
      
      (* Brief sleep *)
      Unix.sleepf 0.001  (* 1ms polling *)
    done;
    
    Printf.printf "[Runtime] Shutting down runtime\n"
  
  let stop_runtime runtime =
    runtime.should_stop <- true;
    Hashtbl.iter (fun _ bot -> BotProcess.kill_bot bot) runtime.active_bots
end

(* ========== Example Bot Configurations ========== *)

module BotConfigs = struct
  
  let coq_gym_config = BotProcess.CoqGymBot "/path/to/coqgym/model"
  let prover_bot_config = BotProcess.ProverBot "/usr/local/bin/proverbot9001"
  let tactic_toe_config = BotProcess.TacticToeBot "/usr/local/bin/tactictoe"
  let coq_hammer_config = BotProcess.CoqHammerBot
  
  (* Create a standard crypto proof bot farm *)
  let create_crypto_farm runtime =
    let configs = [
      ("coqgym_crypto", coq_gym_config, ["cryptography"; "formal_verification"]);
      ("proverbot_crypto", prover_bot_config, ["automated_proving"; "cryptography"]);
      ("tactictoe_crypto", tactic_toe_config, ["tactic_synthesis"; "cryptography"]);
      ("hammer_crypto", coq_hammer_config, ["automated_theorem_proving"]);
    ] in
    
    List.iter (fun (name, executable, capabilities) ->
      match BotRuntime.start_bot runtime ~name ~executable ~capabilities with
      | Ok entry -> 
          Printf.printf "[Config] Started %s at 0x%Lx\n" name entry.address
      | Error err -> 
          Printf.printf "[Config] Failed to start %s: %s\n" name err
    ) configs
end

(* ========== Main Runtime Entry Point ========== *)

let main () =
  Printf.printf "=== AutoProver Bot Runtime Engine ===\n";
  
  (* Create runtime with formally verified NVS *)
  let runtime = BotRuntime.create_runtime (10 * 1024 * 1024) in
  
  (* Start crypto proof bot farm *)
  BotConfigs.create_crypto_farm runtime;
  
  (* Set up signal handlers *)
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ ->
    Printf.printf "\n[Runtime] Received SIGINT, shutting down...\n";
    BotRuntime.stop_runtime runtime
  ));
  
  (* Run the runtime *)
  BotRuntime.run_runtime runtime;
  
  Printf.printf "[Runtime] Shutdown complete\n"

(* Start runtime if this is the main module *)
let () = 
  if !Sys.interactive = false then main ()