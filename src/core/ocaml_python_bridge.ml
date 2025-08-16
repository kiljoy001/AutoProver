(*
 * OCaml-Python Bridge for Maximum Parallelism
 * OCaml orchestrates Python bot execution with true parallelism
 *)

open Unix
open Printf
open Str

(* ========== Process Management Types ========== *)

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

type parallel_coordinator = {
  mutable active_processes: (int * bot_spec) list;
  mutable completed_results: execution_result list;
  mutable max_parallel: int;
  goal: string;
}

(* ========== OCaml Process Pool ========== *)

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
      
      (* Add to active processes *)
      coordinator.active_processes <- (pid, bot_spec) :: coordinator.active_processes;
      
      (* Return file descriptors for reading results *)
      (pid, out_read, err_read)
      
    with
    | Unix_error(err, func, arg) ->
        printf "[OCaml-Bridge] ❌ Failed to spawn %s: %s in %s(%s)\n%!" 
          bot_spec.bot_name (error_message err) func arg;
        failwith "Process spawn failed"
  
  let read_bot_result pid out_fd err_fd bot_spec start_time =
    try
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
          (* Simple JSON parsing (would use a proper library in production) *)
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
          
          {
            bot_name = bot_spec.bot_name;
            success = success;
            tactic = tactic;
            confidence = confidence;
            execution_time = execution_time;
            process_id = pid;
            error = error_output;
          }
          
        with _ ->
          {
            bot_name = bot_spec.bot_name;
            success = false;
            tactic = "parse_error";
            confidence = 0.0;
            execution_time = execution_time;
            process_id = pid;
            error = Some ("Parse error: " ^ output);
          }
      ) else (
        {
          bot_name = bot_spec.bot_name;
          success = false;
          tactic = "no_output";
          confidence = 0.0;
          execution_time = execution_time;
          process_id = pid;
          error = Some "No output from bot";
        }
      )
      
    with
    | Unix_error(EAGAIN, _, _) | Unix_error(EWOULDBLOCK, _, _) ->
        (* Non-blocking read would block, process still running *)
        {
          bot_name = bot_spec.bot_name;
          success = false;
          tactic = "still_running";
          confidence = 0.0;
          execution_time = Unix.time () -. start_time;
          process_id = pid;
          error = Some "Process still running";
        }
    | e ->
        let execution_time = Unix.time () -. start_time in
        {
          bot_name = bot_spec.bot_name;
          success = false;
          tactic = "read_error";
          confidence = 0.0;
          execution_time = execution_time;
          process_id = pid;
          error = Some (Printexc.to_string e);
        }
  
  let execute_bots_maximum_parallel goal selected_bots =
    printf "[OCaml-Bridge] 🔥 MAXIMUM PARALLELISM: OCaml coordinating %d Python bots\n%!" (List.length selected_bots);
    printf "[OCaml-Bridge] 🎯 Goal: %s\n%!" (String.sub goal 0 (min 50 (String.length goal)));
    
    let coordinator = create_coordinator goal (List.length selected_bots) in
    let start_time = Unix.time () in
    
    (* Step 1: Spawn ALL bots simultaneously *)
    let spawned_processes = List.map (fun bot_spec ->
      try
        let (pid, out_fd, err_fd) = spawn_python_bot coordinator bot_spec in
        Some (pid, out_fd, err_fd, bot_spec, start_time)
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
            let (still_running, timed_out) = List.partition (fun (pid, _, _, bot_spec, start) ->
              (current_time -. start) < bot_spec.max_execution_time
            ) processes in
            
            (* Kill timed out processes *)
            List.iter (fun (pid, out_fd, err_fd, bot_spec, start) ->
              printf "[OCaml-Bridge] ⏰ Killing timed out process %s (PID %d)\n%!" bot_spec.bot_name pid;
              (try kill pid Sys.sigterm with _ -> ());
              close out_fd;
              close err_fd;
            ) timed_out;
            
            monitor_processes still_running completed_results
          ) else (
            (* Some processes are ready *)
            let (ready_processes, still_waiting) = List.partition (fun (_, out_fd, _, _, _) ->
              List.mem out_fd ready_fds
            ) processes in
            
            (* Read results from ready processes *)
            let new_results = List.map (fun (pid, out_fd, err_fd, bot_spec, start) ->
              let result = read_bot_result pid out_fd err_fd bot_spec start in
              (* Wait for process to finish *)
              (try ignore (waitpid [] pid) with _ -> ());
              result
            ) ready_processes in
            
            monitor_processes still_waiting (new_results @ completed_results)
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
    printf "  Fastest bot: %.3fs\n%!" fastest_time;
    printf "  Parallel efficiency: %.1fx speedup\n%!" 
      (if total_time > 0.0 then (List.length all_results |> float_of_int) *. fastest_time /. total_time else 1.0);
    
    all_results

end

(* ========== GhostDAG Integration ========== *)

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
  printf "🔗 OCaml-Python Bridge for Maximum Parallelism\n%!";
  printf "🔥 OCaml will coordinate Python bot execution\n%!";
  
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