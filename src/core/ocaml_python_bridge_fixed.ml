(*
 * Fixed OCaml-Python Bridge for Maximum Parallelism
 * Implements the type-safe solution proven in autoprover_core_fix.v
 *)

open Unix
open Printf
open Str

(* ========== Process Management Types (FIXED) ========== *)

type bot_spec = {
  bot_name: string;
  bot_type: string;
  python_script: string;
  max_execution_time: float;
}

type execution_result = {
  bot_name: string;
  success: bool;
  tactic: string;
  confidence: float;
  execution_time: float;
  process_id: int;
  error: string option;
}

(* FIXED: Separate process state from bot specification *)
type process_state = 
  | Spawned
  | Running of bot_spec * float  (* bot_spec and start_time *)
  | Completed of execution_result
  | Timed_out of bot_spec
  | Failed of string

(* FIXED: Correct tuple structure with separated types *)
type process_tuple = (int * Unix.file_descr * Unix.file_descr * process_state * float)

type parallel_coordinator = {
  mutable active_processes: process_tuple list;
  mutable completed_results: execution_result list;
  mutable max_parallel: int;
  goal: string;
}

(* ========== OCaml Process Pool (FIXED) ========== *)

module OCamlProcessPool = struct
  
  let create_coordinator goal max_parallel =
    {
      active_processes = [];
      completed_results = [];
      max_parallel = max_parallel;
      goal = goal;
    }
  
  let available_bots = [
    {
      bot_name = "coqgym_gpu";
      bot_type = "gpu_accelerated";
      python_script = "/home/scott/Repo/AutoProver/src/bots/gpu_coqgym_bot.py";
      max_execution_time = 10.0;
    };
    {
      bot_name = "coqgym_cpu";
      bot_type = "cpu_inference";
      python_script = "/home/scott/Repo/AutoProver/src/bots/real_coqgym_bot.py";
      max_execution_time = 5.0;
    };
    {
      bot_name = "proverbot9001";
      bot_type = "complete_proof";
      python_script = "/home/scott/Repo/AutoProver/src/bots/real_proverbot_bot.py";
      max_execution_time = 30.0;
    };
  ]
  
  let spawn_python_bot (coordinator : parallel_coordinator) (bot_spec : bot_spec) =
    printf "[OCaml-Bridge] 🚀 Spawning %s (PID will be assigned)\n%!" bot_spec.bot_name;
    
    try
      (* Create pipes for communication *)
      let (in_read, in_write) = pipe () in
      let (out_read, out_write) = pipe () in
      let (err_read, err_write) = pipe () in
      
      (* Fork process *)
      let pid = create_process "python3" [|"python3"; bot_spec.python_script|] in_read out_write err_write in
      
      (* Close unused pipe ends *)
      close in_read;
      close out_write;
      close err_write;
      
      (* Send goal to bot *)
      let goal_with_newline = coordinator.goal ^ "\n" in
      let bytes_written = write in_write (Bytes.of_string goal_with_newline) 0 (String.length goal_with_newline) in
      close in_write;
      
      printf "[OCaml-Bridge] ✅ Spawned %s with PID %d, sent %d bytes\n%!" bot_spec.bot_name pid bytes_written;
      
      let start_time = Unix.time () in
      (* FIXED: Create correct tuple with process state *)
      let process_tuple = (pid, out_read, err_read, Running (bot_spec, start_time), start_time) in
      
      (* Add to active processes *)
      coordinator.active_processes <- process_tuple :: coordinator.active_processes;
      
      (* Return process tuple *)
      process_tuple
      
    with
    | Unix_error(err, func, arg) ->
        printf "[OCaml-Bridge] ❌ Failed to spawn %s: %s in %s(%s)\n%!" 
          bot_spec.bot_name (error_message err) func arg;
        failwith "Process spawn failed"
  
  let read_bot_result process_tuple =
    let (pid, out_fd, err_fd, state, creation_time) = process_tuple in
    match state with
    | Running (bot_spec, start_time) ->
        (try
          (* Set non-blocking read *)
          set_nonblock out_fd;
          set_nonblock err_fd;
          
          (* Read stdout (bot result) *)
          let buffer = Bytes.create 4096 in
          let bytes_read = read out_fd buffer 0 4096 in
          let output = Bytes.sub_string buffer 0 bytes_read in
          
          (* Read stderr (logs) *)
          let err_buffer = Bytes.create 1024 in
          let err_bytes = try read err_fd err_buffer 0 1024 with _ -> 0 in
          let error_output = if err_bytes > 0 then Some (Bytes.sub_string err_buffer 0 err_bytes) else None in
          
          close out_fd;
          close err_fd;
          
          (* Parse JSON result from Python bot *)
          let execution_time = Unix.time () -. start_time in
          
          printf "[OCaml-Bridge] 📥 Read %d bytes from %s (PID %d) in %.3fs\n%!" 
            bytes_read bot_spec.bot_name pid execution_time;
          
          if String.length output > 0 then (
            try
              (* Simple JSON parsing *)
              let has_tactic = String.contains output '"' && String.contains output ':' in
              let contains_error = 
                try 
                  let _ = Str.search_forward (Str.regexp "error\\|Error\\|ERROR") output 0 in
                  true
                with Not_found -> false in
              let success = has_tactic && not contains_error in
              
              (* Extract tactic (simplified) *)
              let tactic = 
                if success then
                  try
                    let start_pos = String.index output '"' + 1 in
                    let end_pos = String.index_from output start_pos '"' in
                    String.sub output start_pos (end_pos - start_pos)
                  with _ -> "auto."
                else "failed"
              in
              
              (* Extract confidence (simplified) *)
              let confidence = if success then 0.8 else 0.0 in
              
              let result = {
                bot_name = bot_spec.bot_name;
                success = success;
                tactic = tactic;
                confidence = confidence;
                execution_time = execution_time;
                process_id = pid;
                error = error_output;
              } in
              
              (* FIXED: Return completed state with result *)
              (pid, out_fd, err_fd, Completed result, creation_time)
              
            with _ ->
              let result = {
                bot_name = bot_spec.bot_name;
                success = false;
                tactic = "parse_error";
                confidence = 0.0;
                execution_time = execution_time;
                process_id = pid;
                error = Some ("Parse error: " ^ output);
              } in
              (pid, out_fd, err_fd, Completed result, creation_time)
          ) else (
            let result = {
              bot_name = bot_spec.bot_name;
              success = false;
              tactic = "no_output";
              confidence = 0.0;
              execution_time = execution_time;
              process_id = pid;
              error = Some "No output from bot";
            } in
            (pid, out_fd, err_fd, Completed result, creation_time)
          )
          
        with
        | Unix_error(EAGAIN, _, _) | Unix_error(EWOULDBLOCK, _, _) ->
            (* Non-blocking read would block, process still running *)
            process_tuple  (* Return unchanged *)
        | e ->
            let result = {
              bot_name = bot_spec.bot_name;
              success = false;
              tactic = "read_error";
              confidence = 0.0;
              execution_time = Unix.time () -. start_time;
              process_id = pid;
              error = Some (Printexc.to_string e);
            } in
            (pid, out_fd, err_fd, Completed result, creation_time))
    | _ -> process_tuple  (* Already completed or failed *)
  
  (* FIXED: Type-safe timeout checking *)
  let check_timeout process_tuple current_time =
    let (pid, out_fd, err_fd, state, creation_time) = process_tuple in
    match state with
    | Running (bot_spec, start_time) ->
        if (current_time -. start_time) > bot_spec.max_execution_time then
          Some (pid, out_fd, err_fd, Timed_out bot_spec, creation_time)
        else None
    | _ -> None  (* Only running processes can timeout *)
  
  (* FIXED: Type-safe cleanup *)
  let cleanup_process process_tuple =
    let (pid, out_fd, err_fd, state, creation_time) = process_tuple in
    match state with
    | Running (bot_spec, _) ->
        printf "[OCaml-Bridge] ⏰ Killing timed out process %s (PID %d)\n%!" bot_spec.bot_name pid;
        (try kill pid Sys.sigterm with _ -> ());
        (try close out_fd with _ -> ());
        (try close err_fd with _ -> ())
    | Timed_out bot_spec ->
        printf "[OCaml-Bridge] 🧹 Cleaning up timed out process %s (PID %d)\n%!" bot_spec.bot_name pid;
        (try kill pid Sys.sigterm with _ -> ());
        (try close out_fd with _ -> ());
        (try close err_fd with _ -> ())
    | _ ->
        (* Cleanup completed/failed processes *)
        (try close out_fd with _ -> ());
        (try close err_fd with _ -> ())
  
  let execute_bots_maximum_parallel goal selected_bots =
    printf "[OCaml-Bridge] 🔥 MAXIMUM PARALLELISM: OCaml coordinating %d Python bots\n%!" (List.length selected_bots);
    printf "[OCaml-Bridge] 🎯 Goal: %s\n%!" (String.sub goal 0 (min 50 (String.length goal)));
    
    let coordinator = create_coordinator goal (List.length selected_bots) in
    let start_time = Unix.time () in
    
    (* Step 1: Spawn ALL bots simultaneously *)
    let spawned_processes = List.map (fun bot_spec ->
      try
        Some (spawn_python_bot coordinator bot_spec)
      with e ->
        printf "[OCaml-Bridge] ❌ Failed to spawn %s: %s\n%!" bot_spec.bot_name (Printexc.to_string e);
        None
    ) selected_bots in
    
    let active_processes = List.filter_map (fun x -> x) spawned_processes in
    
    printf "[OCaml-Bridge] ⚡ Spawned %d/%d bots successfully\n%!" 
      (List.length active_processes) (List.length selected_bots);
    
    (* Step 2: Monitor processes with select() for maximum efficiency *)
    let rec monitor_processes remaining_processes completed_results =
      match remaining_processes with
      | [] -> completed_results
      | processes ->
          (* Use select to wait for any process to complete *)
          let read_fds = List.map (fun (_, out_fd, _, _, _) -> out_fd) processes in
          let (ready_fds, _, _) = select read_fds [] [] 1.0 in (* 1 second timeout *)
          
          if ready_fds = [] then (
            (* Timeout - check for completed processes *)
            let current_time = Unix.time () in
            let (still_running, timed_out) = List.partition (fun proc ->
              match check_timeout proc current_time with
              | None -> true  (* Still running *)
              | Some _ -> false  (* Timed out *)
            ) processes in
            
            (* FIXED: Type-safe cleanup of timed out processes *)
            List.iter cleanup_process timed_out;
            
            monitor_processes still_running completed_results
          ) else (
            (* Some processes are ready - try to read results *)
            let updated_processes = List.map read_bot_result processes in
            
            (* Separate completed from still running *)
            let (completed, still_running) = List.partition (fun (_, _, _, state, _) ->
              match state with
              | Completed _ -> true
              | _ -> false
            ) updated_processes in
            
            (* Extract results from completed processes *)
            let new_results = List.map (fun (_, _, _, state, _) ->
              match state with
              | Completed result -> result
              | _ -> failwith "Logic error: should be completed"
            ) completed in
            
            monitor_processes still_running (new_results @ completed_results)
          )
    in
    
    (* Step 3: Collect all results *)
    let all_results = monitor_processes active_processes [] in
    let total_time = Unix.time () -. start_time in
    
    (* Step 4: Statistics *)
    let successful_results = List.filter (fun r -> r.success) all_results in
    let fastest_time = List.fold_left (fun acc r -> min acc r.execution_time) max_float all_results in
    
    printf "[OCaml-Bridge] 📊 PARALLEL EXECUTION COMPLETE:\n%!";
    printf "  Total time: %.3fs\n%!" total_time;
    printf "  Successful: %d/%d bots\n%!" (List.length successful_results) (List.length all_results);
    if List.length all_results > 0 then
      printf "  Fastest bot: %.3fs\n%!" fastest_time;
    printf "  Parallel efficiency: %.1fx speedup\n%!" 
      (if total_time > 0.0 then (List.length all_results |> float_of_int) *. fastest_time /. total_time else 1.0);
    
    all_results

end

(* ========== GhostDAG Integration (UNCHANGED) ========== *)

module GhostDAGOCamlBridge = struct
  
  let select_best_result_by_consensus results =
    printf "[OCaml-Bridge] 🔗 Applying GhostDAG consensus to %d results\n%!" (List.length results);
    
    let successful_results = List.filter (fun r -> r.success) results in
    
    match successful_results with
    | [] -> 
        printf "[OCaml-Bridge] ❌ No successful results for consensus\n%!";
        None
    | results ->
        (* Simple consensus: highest confidence + fastest execution *)
        let scored_results = List.map (fun r ->
          let speed_bonus = 1.0 /. (r.execution_time +. 0.001) *. 0.1 in
          let consensus_score = r.confidence +. speed_bonus in
          (r, consensus_score)
        ) results in
        
        let sorted = List.sort (fun (_, s1) (_, s2) -> compare s2 s1) scored_results in
        let (best_result, best_score) = List.hd sorted in
        
        printf "[OCaml-Bridge] 🏆 Consensus winner: %s (score: %.3f, confidence: %.3f)\n%!" 
          best_result.bot_name best_score best_result.confidence;
        
        Some best_result
  
  let ocaml_coordinated_proof_attempt goal =
    printf "[OCaml-Bridge] 🚀 OCaml-coordinated parallel proof attempt\n%!";
    printf "[OCaml-Bridge] 🎯 Goal: %s\n%!" goal;
    
    (* Execute all available bots in parallel *)
    let results = OCamlProcessPool.execute_bots_maximum_parallel goal OCamlProcessPool.available_bots in
    
    (* Apply GhostDAG consensus *)
    select_best_result_by_consensus results

end

(* ========== Main Entry Point ========== *)

let () =
  printf "🔗 FIXED OCaml-Python Bridge for Maximum Parallelism\n%!";
  printf "🔥 Type-safe OCaml coordination based on formal proofs\n%!";
  
  (* Test with a sample goal *)
  let test_goal = "forall n : nat, n + 0 = n" in
  
  match GhostDAGOCamlBridge.ocaml_coordinated_proof_attempt test_goal with
  | Some result ->
      printf "\n🏆 FINAL RESULT:\n%!";
      printf "  Bot: %s\n%!" result.bot_name;
      printf "  Tactic: %s\n%!" result.tactic;
      printf "  Confidence: %.3f\n%!" result.confidence;
      printf "  Time: %.3fs\n%!" result.execution_time;
      printf "  Success: %s\n%!" (if result.success then "✅" else "❌");
  | None ->
      printf "\n❌ No successful result from parallel execution\n%!"