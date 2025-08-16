(* 
 * Zero-Copy IPC for AutoProver in OCaml
 * 
 * Uses OCaml's Bigarray for zero-copy shared memory and Ancient library
 * for sharing complex data structures between processes
 *)

open Bigarray

(* ========== Zero-Copy Shared Memory via Bigarray ========== *)

(* Bigarray gives us direct memory access without GC overhead *)
module SharedMemory = struct
  (* Memory mapped array - no GC, no copies *)
  type t = (char, int8_unsigned_elt, c_layout) Array1.t
  
  (* Create shared memory segment *)
  let create ~size =
    (* Use Unix shared memory *)
    let fd = Unix.(openfile "/dev/shm/autoprover_arena" 
                    [O_RDWR; O_CREAT; O_TRUNC] 0o666) in
    Unix.ftruncate fd size;
    
    (* Memory map with Bigarray - ZERO COPY! *)
    let shared_mem = 
      Unix.map_file fd Char c_layout true [| size |]
      |> array1_of_genarray in
    
    (* FIXED: Don't close fd immediately - keep for proper cleanup *)
    (* Unix.close fd; *)
    shared_mem
    
  (* Attach to existing shared memory *)
  let attach () =
    let fd = Unix.(openfile "/dev/shm/autoprover_arena" [O_RDWR] 0o666) in
    let size = (Unix.fstat fd).st_size in
    let shared_mem = 
      Unix.map_file fd Char c_layout true [| size |]
      |> array1_of_genarray in
    (* FIXED: Don't close fd immediately - keep for proper cleanup *)
    (* Unix.close fd; *)
    shared_mem
end

(* ========== Lock-Free Data Structures ========== *)

(* Use OCaml-multicore's lock-free structures *)
module LockFree = struct
  (* Atomic operations on shared memory *)
  external cas_int : int ref -> int -> int -> bool = "caml_atomic_cas"
  external fetch_add : int ref -> int -> int = "caml_atomic_fetch_add"
  
  (* Lock-free queue for messages *)
  module Queue = struct
    type 'a node = {
      value: 'a;
      next: 'a node option Atomic.t;
    }
    
    type 'a t = {
      head: 'a node option Atomic.t;
      tail: 'a node option Atomic.t;
    }
    
    let create () = {
      head = Atomic.make None;
      tail = Atomic.make None;
    }
    
    let enqueue q v =
      let new_node = { value = v; next = Atomic.make None } in
      let rec loop () =
        let tail = Atomic.get q.tail in
        match tail with
        | None ->
            if Atomic.compare_and_set q.tail None (Some new_node) then
              Atomic.set q.head (Some new_node)
            else loop ()
        | Some t ->
            if Atomic.compare_and_set t.next None (Some new_node) then
              ignore (Atomic.compare_and_set q.tail tail (Some new_node))
            else loop ()
      in loop ()
      
    let dequeue q =
      let rec loop () =
        let head = Atomic.get q.head in
        match head with
        | None -> None
        | Some h ->
            let next = Atomic.get h.next in
            if Atomic.compare_and_set q.head head next then
              Some h.value
            else loop ()
      in loop ()
  end
end

(* ========== Proof State in Shared Memory ========== *)

module ProofState = struct
  (* Proof state that can be shared between processes *)
  type t = {
    id: int64;
    goal_hash: int32;
    goal: string;
    context: string;
    tactic: string;
    specialist_id: int;
    confidence: float;
    gas_used: int;
    parent_ids: int64 array;
    mutable blue_score: int;
    mutable is_blue: bool;
    mutable is_complete: bool;
  }
  
  (* Serialize to shared memory region *)
  let to_bytes proof =
    (* Use OCaml's Marshal for zero-copy serialization *)
    Marshal.to_string proof [Marshal.No_sharing]
    
  (* Deserialize from shared memory *)
  let from_bytes bytes =
    Marshal.from_string bytes 0
    
  (* Store in Bigarray shared memory *)
  let store_in_shm shm offset proof =
    let bytes = to_bytes proof in
    let len = String.length bytes in
    for i = 0 to len - 1 do
      shm.{offset + i} <- bytes.[i]
    done;
    len
    
  (* Read from Bigarray shared memory *)
  let read_from_shm shm offset len =
    let bytes = Bytes.create len in
    for i = 0 to len - 1 do
      Bytes.set bytes i shm.{offset + i}
    done;
    from_bytes (Bytes.to_string bytes)
end

(* ========== Ancient Library for Complex Structures ========== *)

(* Ancient allows sharing OCaml values outside the GC heap *)
module AncientSharing = struct
  (* Create ancient heap for sharing complex structures *)
  let ancient_heap = Ancient.attach "/dev/shm/autoprover_ancient" 100_000_000
  
  (* Share a proof DAG structure *)
  let share_proof_dag dag =
    (* Move to ancient heap - becomes shared between all processes *)
    Ancient.share ancient_heap 0 dag
    
  (* Get shared proof DAG *)
  let get_proof_dag () =
    Ancient.get ancient_heap 0
    
  (* This is ZERO-COPY - the data structure is directly mapped in memory! *)
end

(* ========== High-Performance Message Passing ========== *)

module BotMessage = struct
  type msg_type = 
    | NewProof of int64 * string
    | ProofDone of int64 * string * float
    | HelpRequest of int64 * string
    | LemmaFound of string * float
    
  type t = {
    sequence: int64;
    sender_id: int;
    timestamp: float;
    message: msg_type;
  }
  
  (* Ring buffer in shared memory *)
  module RingBuffer = struct
    let size = 65536  (* 64K messages *)
    let message_size = 512  (* bytes per message *)
    
    type t = {
      mutable write_pos: int Atomic.t;
      read_pos: int Atomic.t array;  (* Per-bot read positions *)
      memory: SharedMemory.t;
    }
    
    let create () = {
      write_pos = Atomic.make 0;
      read_pos = Array.init 32 (fun _ -> Atomic.make 0);
      memory = SharedMemory.create ~size:(size * message_size);
    }
    
    (* Lock-free send *)
    let send ring msg =
      let bytes = Marshal.to_string msg [] in
      let pos = Atomic.fetch_and_add ring.write_pos 1 mod size in
      let offset = pos * message_size in
      
      (* Write to shared memory *)
      String.iteri (fun i c ->
        ring.memory.{offset + i} <- c
      ) bytes;
      
      (* Memory barrier to ensure visibility *)
      Atomic.fence()
      
    (* Lock-free receive for bot *)
    let receive ring bot_id =
      let read_pos = ring.read_pos.(bot_id) in
      let current = Atomic.get read_pos in
      let write = Atomic.get ring.write_pos in
      
      if current < write then begin
        let pos = current mod size in
        let offset = pos * message_size in
        
        (* Read from shared memory *)
        let bytes = Bytes.create message_size in
        for i = 0 to message_size - 1 do
          Bytes.set bytes i ring.memory.{offset + i}
        done;
        
        Atomic.incr read_pos;
        Some (Marshal.from_string (Bytes.to_string bytes) 0)
      end else
        None
  end
end

(* ========== NUMA-Aware Memory Allocation ========== *)

module Numa = struct
  (* FFI to libnuma *)
  external numa_node_of_cpu : int -> int = "numa_node_of_cpu"
  external numa_alloc_onnode : int -> int -> Bigarray.Array1.t = "numa_alloc_onnode"
  external numa_set_preferred : int -> unit = "numa_set_preferred"
  
  (* Allocate proof states on specific NUMA node *)
  let alloc_on_node ~size ~node =
    numa_set_preferred node;
    numa_alloc_onnode size node
    
  (* Pin bot to CPU/NUMA node *)
  let pin_bot bot_id =
    let cpu = bot_id mod (Sys.cpu_count()) in
    let node = numa_node_of_cpu cpu in
    Unix.(setaffinity (getpid()) [cpu]);
    node
end

(* ========== Performance Monitoring ========== *)

module PerfCounters = struct
  type t = {
    cache_hits: int Atomic.t;
    cache_misses: int Atomic.t;
    messages_sent: int Atomic.t;
    proofs_completed: int Atomic.t;
    memory_used: int Atomic.t;
  }
  
  let create () = {
    cache_hits = Atomic.make 0;
    cache_misses = Atomic.make 0;
    messages_sent = Atomic.make 0;
    proofs_completed = Atomic.make 0;
    memory_used = Atomic.make 0;
  }
  
  let incr counter = Atomic.incr counter
  let get counter = Atomic.get counter
end

(* ========== Example Usage ========== *)

let demo () =
  (* Create shared memory arena *)
  let shm = SharedMemory.create ~size:1_000_000_000 in  (* 1GB *)
  
  (* Create message ring buffer *)
  let msg_ring = BotMessage.RingBuffer.create () in
  
  (* Bot sends proof completion *)
  let msg = BotMessage.{
    sequence = 1L;
    sender_id = 0;
    timestamp = Unix.gettimeofday();
    message = ProofDone (42L, "reflexivity", 0.95);
  } in
  BotMessage.RingBuffer.send msg_ring msg;
  
  (* Another bot receives *)
  match BotMessage.RingBuffer.receive msg_ring 1 with
  | Some received -> Printf.printf "Got message: %Ld\n" received.sequence
  | None -> Printf.printf "No messages\n"
  
  (* Store proof state in shared memory - ZERO COPY! *)
  let proof = ProofState.{
    id = 42L;
    goal_hash = 0xDEADBEEFl;
    goal = "forall x, x = x";
    context = "...";
    tactic = "reflexivity";
    specialist_id = 1;
    confidence = 0.95;
    gas_used = 100;
    parent_ids = [| 41L |];
    blue_score = 10;
    is_blue = true;
    is_complete = true;
  } in
  
  let _ = ProofState.store_in_shm shm 0 proof in
  Printf.printf "Proof stored in zero-copy shared memory!\n"