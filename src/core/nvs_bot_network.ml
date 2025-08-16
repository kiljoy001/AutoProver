(*
 * NVS-Style Bot Network with FSM Packet Protocol
 * 
 * Each bot has an Emercoin NVS-style address pointing to its IPC memory region
 * Messages are FSM-formatted byte array packets, like a network protocol
 *)

open Bigarray

(* ========== NVS-Style Bot Registry ========== *)

module BotNVS = struct
  
  (* NVS entry for a bot *)
  type nvs_entry = {
    name: string;           (* e.g., "bot:coqgym:induction:01" *)
    address: int64;         (* IPC memory address *)
    shm_offset: int;        (* Offset in shared memory *)
    inbox_size: int;        (* Size of message inbox *)
    status: [`Active | `Idle | `Busy | `Dead];
    capabilities: string list;  (* What this bot can do *)
    pubkey: bytes;          (* For message authentication *)
  }
  
  (* Global NVS registry in shared memory *)
  type registry = {
    memory: (char, int8_unsigned_elt, c_layout) Array1.t;
    entries: (string, nvs_entry) Hashtbl.t;
    next_offset: int Atomic.t;
  }
  
  (* Create NVS registry *)
  let create_registry size =
    let fd = Unix.openfile "/dev/shm/autoprover_nvs" 
              [Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC] 0o666 in
    Unix.ftruncate fd size;
    
    let memory = Unix.map_file fd char c_layout true [| size |]
                 |> array1_of_genarray in
    
    { memory;
      entries = Hashtbl.create 256;
      next_offset = Atomic.make 0;
    }
  
  (* Register a bot in NVS *)
  let register_bot registry ~name ~capabilities =
    (* Allocate memory region for bot's inbox *)
    let inbox_size = 65536 in  (* 64KB inbox per bot *)
    let offset = Atomic.fetch_and_add registry.next_offset inbox_size in
    
    (* Generate bot keypair for authentication *)
    let pubkey = Bytes.create 32 in
    (* In real implementation, generate actual keypair *)
    
    let entry = {
      name;
      address = Int64.of_int offset;
      shm_offset = offset;
      inbox_size;
      status = `Idle;
      capabilities;
      pubkey;
    } in
    
    Hashtbl.add registry.entries name entry;
    
    Printf.printf "[NVS] Registered bot '%s' at address 0x%Lx (offset: %d)\n"
      name entry.address offset;
    
    entry
  
  (* Lookup bot by name *)
  let lookup registry name =
    try Some (Hashtbl.find registry.entries name)
    with Not_found -> None
  
  (* Update bot status *)
  let update_status registry name status =
    match lookup registry name with
    | Some entry ->
        let updated = { entry with status } in
        Hashtbl.replace registry.entries name updated
    | None -> ()
end

(* ========== FSM Packet Format ========== *)

module FSMPacket = struct
  
  (* Packet types - like network protocol *)
  type packet_type =
    | PROOF_REQUEST     (* 0x01 - Request to prove something *)
    | PROOF_RESPONSE    (* 0x02 - Result of proof attempt *)
    | TACTIC_SUGGEST    (* 0x03 - Suggest a tactic *)
    | STATE_UPDATE      (* 0x04 - Update proof state *)
    | HEARTBEAT         (* 0x05 - Keep-alive *)
    | DISCOVERY         (* 0x06 - Service discovery *)
    | CONSENSUS_VOTE    (* 0x07 - Vote on best tactic *)
    | CACHE_QUERY       (* 0x08 - Check Solr cache *)
    | CACHE_RESPONSE    (* 0x09 - Solr results *)
    | ERROR             (* 0xFF - Error message *)
  
  (* FSM states for packet processing *)
  type fsm_state =
    | IDLE
    | RECEIVING_HEADER
    | RECEIVING_PAYLOAD
    | PROCESSING
    | SENDING_RESPONSE
    | ERROR_STATE
  
  (* Packet header - fixed 32 bytes *)
  type header = {
    magic: int32;           (* 0x50524F46 = "PROF" *)
    version: int8;          (* Protocol version *)
    packet_type: int8;      (* Packet type *)
    flags: int16;           (* Flags/options *)
    sequence: int32;        (* Sequence number *)
    sender_addr: int64;     (* Sender's NVS address *)
    dest_addr: int64;       (* Destination NVS address *)
    payload_size: int32;    (* Size of payload *)
    checksum: int32;        (* CRC32 of payload *)
  }
  
  (* Complete packet *)
  type packet = {
    header: header;
    payload: bytes;
  }
  
  (* Serialize header to bytes - network byte order *)
  let serialize_header h =
    let buf = Bytes.create 32 in
    
    (* Magic number *)
    Bytes.set_int32_be buf 0 h.magic;
    
    (* Version and type *)
    Bytes.set buf 4 (Char.chr h.version);
    Bytes.set buf 5 (Char.chr h.packet_type);
    
    (* Flags *)
    Bytes.set_int16_be buf 6 h.flags;
    
    (* Sequence *)
    Bytes.set_int32_be buf 8 h.sequence;
    
    (* Addresses *)
    Bytes.set_int64_be buf 12 h.sender_addr;
    Bytes.set_int64_be buf 20 h.dest_addr;
    
    (* Payload size and checksum *)
    Bytes.set_int32_be buf 28 h.payload_size;
    
    buf
  
  (* Deserialize header from bytes *)
  let deserialize_header buf =
    if Bytes.length buf < 32 then
      failwith "Invalid header size";
    
    {
      magic = Bytes.get_int32_be buf 0;
      version = Char.code (Bytes.get buf 4);
      packet_type = Char.code (Bytes.get buf 5);
      flags = Bytes.get_int16_be buf 6;
      sequence = Bytes.get_int32_be buf 8;
      sender_addr = Bytes.get_int64_be buf 12;
      dest_addr = Bytes.get_int64_be buf 20;
      payload_size = Bytes.get_int32_be buf 28;
      checksum = 0l;  (* Will be computed *)
    }
  
  (* Create proof request packet *)
  let create_proof_request ~sender ~dest ~goal =
    let payload = Bytes.of_string goal in
    let header = {
      magic = 0x50524F46l;  (* "PROF" *)
      version = 1;
      packet_type = 0x01;  (* PROOF_REQUEST *)
      flags = 0;
      sequence = Random.int32 Int32.max_int;
      sender_addr = sender;
      dest_addr = dest;
      payload_size = Int32.of_int (Bytes.length payload);
      checksum = 0l;  (* TODO: compute CRC32 *)
    } in
    { header; payload }
  
  (* Packet type to int *)
  let packet_type_to_int = function
    | PROOF_REQUEST -> 0x01
    | PROOF_RESPONSE -> 0x02
    | TACTIC_SUGGEST -> 0x03
    | STATE_UPDATE -> 0x04
    | HEARTBEAT -> 0x05
    | DISCOVERY -> 0x06
    | CONSENSUS_VOTE -> 0x07
    | CACHE_QUERY -> 0x08
    | CACHE_RESPONSE -> 0x09
    | ERROR -> 0xFF
end

(* ========== Bot Message Inbox (Zero-Copy) ========== *)

module BotInbox = struct
  
  (* Circular buffer for messages *)
  type inbox = {
    memory: (char, int8_unsigned_elt, c_layout) Array1.t;
    offset: int;        (* Offset in shared memory *)
    size: int;          (* Total size *)
    mutable read_pos: int;
    mutable write_pos: int;
    lock: Mutex.t;
  }
  
  (* Create inbox at specific memory offset *)
  let create memory offset size =
    {
      memory;
      offset;
      size;
      read_pos = 0;
      write_pos = 0;
      lock = Mutex.create ();
    }
  
  (* Write packet to inbox - zero copy *)
  let send_packet inbox packet =
    Mutex.lock inbox.lock;
    
    (* Serialize header *)
    let header_bytes = FSMPacket.serialize_header packet.FSMPacket.header in
    
    (* Calculate space needed *)
    let total_size = 32 + Bytes.length packet.payload in
    
    (* Check if fits *)
    if total_size > inbox.size then begin
      Mutex.unlock inbox.lock;
      failwith "Packet too large for inbox"
    end;
    
    (* Write header to shared memory *)
    for i = 0 to 31 do
      inbox.memory.{inbox.offset + inbox.write_pos + i} <- Bytes.get header_bytes i
    done;
    
    (* Write payload *)
    let payload_start = inbox.write_pos + 32 in
    Bytes.iteri (fun i c ->
      inbox.memory.{inbox.offset + payload_start + i} <- c
    ) packet.payload;
    
    (* Update write position - FIXED: Check bounds instead of using modulo *)
    if inbox.write_pos + total_size > inbox.size then
      failwith "Inbox overflow - packet too large"
    else
      inbox.write_pos <- inbox.write_pos + total_size;
    
    Mutex.unlock inbox.lock
  
  (* Receive packet from inbox - zero copy *)
  let receive_packet inbox =
    Mutex.lock inbox.lock;
    
    if inbox.read_pos = inbox.write_pos then begin
      Mutex.unlock inbox.lock;
      None  (* No messages *)
    end else begin
      (* Read header *)
      let header_bytes = Bytes.create 32 in
      for i = 0 to 31 do
        Bytes.set header_bytes i inbox.memory.{inbox.offset + inbox.read_pos + i}
      done;
      
      let header = FSMPacket.deserialize_header header_bytes in
      
      (* Read payload *)
      let payload_size = Int32.to_int header.payload_size in
      let payload = Bytes.create payload_size in
      let payload_start = inbox.read_pos + 32 in
      
      for i = 0 to payload_size - 1 do
        Bytes.set payload i inbox.memory.{inbox.offset + payload_start + i}
      done;
      
      (* Update read position *)
      inbox.read_pos <- (inbox.read_pos + 32 + payload_size) mod inbox.size;
      
      Mutex.unlock inbox.lock;
      
      Some { FSMPacket.header; payload }
    end
end

(* ========== Bot Network Node ========== *)

module BotNode = struct
  
  type t = {
    nvs_entry: BotNVS.nvs_entry;
    inbox: BotInbox.inbox;
    registry: BotNVS.registry;
    mutable fsm_state: FSMPacket.fsm_state;
    handler: (FSMPacket.packet -> FSMPacket.packet option);
  }
  
  (* Create a bot node *)
  let create registry name capabilities handler =
    (* Register in NVS *)
    let nvs_entry = BotNVS.register_bot registry ~name ~capabilities in
    
    (* Create inbox at allocated memory *)
    let inbox = BotInbox.create 
                  registry.memory 
                  nvs_entry.shm_offset 
                  nvs_entry.inbox_size in
    
    {
      nvs_entry;
      inbox;
      registry;
      fsm_state = IDLE;
      handler;
    }
  
  (* Send message to another bot *)
  let send_to bot ~dest_name ~packet_type ~payload =
    match BotNVS.lookup bot.registry dest_name with
    | None -> 
        Printf.printf "[%s] Destination '%s' not found\n" 
          bot.nvs_entry.name dest_name
    
    | Some dest ->
        let packet = {
          FSMPacket.header = {
            magic = 0x50524F46l;
            version = 1;
            packet_type = FSMPacket.packet_type_to_int packet_type;
            flags = 0;
            sequence = Random.int32 Int32.max_int;
            sender_addr = bot.nvs_entry.address;
            dest_addr = dest.address;
            payload_size = Int32.of_int (Bytes.length payload);
            checksum = 0l;
          };
          payload;
        } in
        
        (* Get destination inbox *)
        let dest_inbox = BotInbox.create 
                          bot.registry.memory 
                          dest.shm_offset 
                          dest.inbox_size in
        
        (* Send packet *)
        BotInbox.send_packet dest_inbox packet;
        
        Printf.printf "[%s] Sent %d bytes to %s\n"
          bot.nvs_entry.name 
          (Bytes.length payload)
          dest_name
  
  (* Process incoming messages *)
  let process_messages bot =
    bot.fsm_state <- RECEIVING_HEADER;
    
    match BotInbox.receive_packet bot.inbox with
    | None -> 
        bot.fsm_state <- IDLE
    
    | Some packet ->
        bot.fsm_state <- PROCESSING;
        
        Printf.printf "[%s] Received packet type 0x%02x from 0x%Lx\n"
          bot.nvs_entry.name
          packet.header.packet_type
          packet.header.sender_addr;
        
        (* Call handler *)
        let response = bot.handler packet in
        
        bot.fsm_state <- SENDING_RESPONSE;
        
        (* Send response if any *)
        (match response with
         | Some resp_packet ->
             (* Find sender in NVS *)
             let sender_entry = 
               Hashtbl.fold (fun _ entry acc ->
                 if entry.BotNVS.address = packet.header.sender_addr then
                   Some entry
                 else acc
               ) bot.registry.entries None in
             
             (match sender_entry with
              | Some sender ->
                  let sender_inbox = BotInbox.create
                                      bot.registry.memory
                                      sender.shm_offset
                                      sender.inbox_size in
                  BotInbox.send_packet sender_inbox resp_packet
              | None -> ())
         | None -> ());
        
        bot.fsm_state <- IDLE
  
  (* Run bot event loop *)
  let run bot =
    Printf.printf "[%s] Starting bot at address 0x%Lx\n"
      bot.nvs_entry.name
      bot.nvs_entry.address;
    
    while true do
      process_messages bot;
      Unix.sleepf 0.001  (* 1ms poll interval *)
    done
end

(* ========== Example: Crypto Proof Bot Network ========== *)

module CryptoProofNetwork = struct
  
  (* Create network of specialized crypto proof bots *)
  let create_network () =
    (* Create NVS registry *)
    let registry = BotNVS.create_registry (10 * 1024 * 1024) in  (* 10MB *)
    
    (* Create specialized bots *)
    let bots = [
      (* AES correctness bot *)
      BotNode.create registry 
        "bot:crypto:aes:01"
        ["aes"; "correctness"; "symmetric"]
        (fun packet ->
          let goal = Bytes.to_string packet.payload in
          if String.contains goal "AES" then
            let response = Bytes.of_string "apply AES_correctness_lemma." in
            Some { packet with payload = response }
          else None
        );
      
      (* RSA security bot *)
      BotNode.create registry
        "bot:crypto:rsa:01"
        ["rsa"; "security"; "asymmetric"]
        (fun packet ->
          let goal = Bytes.to_string packet.payload in
          if String.contains goal "RSA" then
            let response = Bytes.of_string "apply RSA_hardness_assumption." in
            Some { packet with payload = response }
          else None
        );
      
      (* Hash collision bot *)
      BotNode.create registry
        "bot:crypto:hash:01"
        ["hash"; "collision"; "sha256"]
        (fun packet ->
          let goal = Bytes.to_string packet.payload in
          if String.contains goal "collision" then
            let response = Bytes.of_string "apply birthday_paradox_bound." in
            Some { packet with payload = response }
          else None
        );
    ] in
    
    (registry, bots)
  
  (* Demo: Send proof request through network *)
  let demo () =
    let (registry, bots) = create_network () in
    
    (* Start bots in separate threads *)
    let threads = List.map (fun bot ->
      Thread.create BotNode.run bot
    ) bots in
    
    (* Send test message *)
    let sender = List.hd bots in
    BotNode.send_to sender
      ~dest_name:"bot:crypto:hash:01"
      ~packet_type:PROOF_REQUEST
      ~payload:(Bytes.of_string "Prove: forall x y, SHA256(x) = SHA256(y) -> x = y");
    
    (* Let network process *)
    Unix.sleep 1;
    
    Printf.printf "\nBot Network Demo Complete!\n"
end

(* ========== Main ========== *)

let () =
  Printf.printf "=== NVS Bot Network with FSM Packets ===\n\n";
  CryptoProofNetwork.demo ()