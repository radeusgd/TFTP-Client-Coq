open Unix
open Arg
open Random
open Bytes
open List
open TFTP_Core


(* explode and implode borrowed from https://github.com/ocaml/ocaml/issues/5367 *)
let explode s =
  let rec exp i l =
  if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (Bytes.length s - 1) []

let implode l =
  let res = Bytes.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> Bytes.set res i c; imp (i + 1) l in
  imp 0 l

let str_to_list (s : string) : char list = explode s
let list_to_str (l : char list) : string = implode l
let fail message = Printf.eprintf "%s\n" message; exit 1

type transfer_direction = Upload of string | Download of string

let parse_args () =
  let ip = ref "" in
  let port = ref 69 in
  let upload = ref "" in
  let download = ref "" in
  Arg.parse [("-ip", Arg.Set_string ip, "IP address of server to connect to"); ("-port", Arg.Set_int port, "port of the server"); ("-download", Arg.Set_string download, "filename to download"); ("-upload", Arg.Set_string upload, "filename to upload")] (fun anon -> Printf.eprintf "Unrecognized argument: %s\n" anon; exit 1) "Simple TFTP client in OCaml and Coq";
  if !ip = "" then fail "IP not specified";
  if !upload = "" && !download = "" then fail "Provide a filename to download or upload";
  if !upload <> "" && !download <> "" then fail "You can either choose download or upload but not both";
  if !upload <> "" then (!ip, !port, Upload !upload)
  else (!ip, !port, Download !download)

let assign_random_TID () : int =
  (* skipping first ports as they tend to require root *)
  (* TODO ranges *)
  Random.int (65535 - 1025) + 1025

let create_udp_socket (tid : int) : file_descr =
  let udp_protocol_type = 17 in
  let recv_timeout = 3.0 in
  let fd = Unix.socket PF_INET SOCK_DGRAM udp_protocol_type in
  let addr = Unix.ADDR_INET (inet_addr_any, tid) in
  Unix.setsockopt_float fd Unix.SO_RCVTIMEO recv_timeout;
  Unix.bind fd addr;
  fd

type state = TFTP_Core.state
type message = bytes
type action
  = Send of message * int
  | Print of string (* these are used mainly for debugging *)
  | RequestRead
  | Write of bytes
  | Terminate
type event
  = Incoming of message * int
  | Read of bytes
  | Timeout (* TODO should also provide IP? *) (*TODO add terminated event*)

let translate_coq_result' (coq_state) : (action list) * state =
  let translate_action coq_action = match coq_action with
    | Coq_send (msg, port) -> Send (list_to_str msg, port)
    | Coq_write msg -> Write (list_to_str msg)
    | Coq_print msg -> Print (list_to_str msg)
    | Coq_request_read -> RequestRead
    | Coq_terminate -> Terminate
  in
  let acts = map translate_action (coq_state.actions) in
  (acts, { coq_state with actions = [] })

let translate_coq_result (coq_result) : (action list) * state =
  match coq_result with
  | Some (coq_state, ()) -> translate_coq_result' coq_state
  | None -> fail "Error, terminating"

let initialize_connection (coq_f) (filename : string) (tid : int) (port : int) : (action list) * state =
  let coq_filename = str_to_list filename in
  (* let init_state = TFTP_Core.initial_state in *)
  translate_coq_result' (coq_f tid port coq_filename)

let process_step (coq_f) (event :  event) (state : state) : (action list) * state =
  let coq_event = match event with
    | Incoming (msg, sender) -> TFTP_Core.Coq_incoming (str_to_list msg, sender)
    | Read msg -> TFTP_Core.Coq_read (str_to_list msg)
    (* | EOF -> TFTP_Core.Coq_eof *)
    | Timeout -> TFTP_Core.Coq_timeout in
  translate_coq_result (coq_f coq_event state)

let max_packet_len = 600

let data_len = TFTP_Core.block_size

let sock_send sockfd toaddr msg =
  let sent = Unix.sendto sockfd msg 0 (Bytes.length msg) [] toaddr in
  if sent <> Bytes.length msg then Printf.eprintf "Warning: message has not been sent whole, shouldn't ever happen with UDP! Sent %d/%d bytes" sent (Bytes.length msg)


let main =
  Random.self_init(); (* initialize randomness *)
  Printf.eprintf "hello world\n";
  let (ip, port, transfer) = parse_args() in
  let tid = assign_random_TID () in
  Printf.eprintf "Connecting to %s:%d, my tid is %d\n%!" ip port tid;
  let sockfd = create_udp_socket tid in
  let filefd = match transfer with
    | Upload fname -> openfile fname [O_RDONLY] 0o664
    | Download fname -> openfile fname [O_WRONLY; O_CREAT; O_TRUNC] 0o664
  in
  let (initialize_connection, process_step) = match transfer with
    | Upload fn -> (initialize_connection TFTP_Core.initialize_upload fn, process_step TFTP_Core.process_step_upload)
    | Download fn -> (initialize_connection TFTP_Core.initialize_download fn, process_step TFTP_Core.process_step_download)
  in
  let make_addr port = ADDR_INET ((inet_addr_of_string ip), port) in
  (* handle action returns whether the process wants to read from file, if any action wants to, file read will start, otherwise the default action will be to wait for the next packet on the network *)
  let handle_action action =
    match action with
    | Terminate -> Printf.eprintf "quitting\n"; exit 0
    | Write data ->
      Printf.eprintf "write %d bytes\n%!" (Bytes.length data);
      let _ = Unix.write filefd data 0 (Bytes.length data) in
      false
    | RequestRead -> true
    | Print msg -> Printf.printf "%s\n%!" msg; false
    | Send (msg, port) ->
      Printf.eprintf "sending '%s' to %d\n%!" (escaped (Bytes.to_string msg)) port;
      let toaddr = make_addr port in
      sock_send sockfd toaddr msg;
      false
  in
  let rec
    receive state =
      Printf.eprintf "waiting for reply\n%!";
      let buf = Bytes.create max_packet_len in
      try
        let (recvd, sender) = Unix.recvfrom sockfd buf 0 max_packet_len [] in
        match sender with
        | ADDR_UNIX _ -> fail "Did not expect a UNIX message on UDP socket!"
        | ADDR_INET (fromip, fromport) ->
          if recvd <= 0 then (* TODO this is not a timeout but terminated conn *)
            (Printf.eprintf "Receive error\n%!";
            loop (process_step Timeout state))
          else
            let msg = Bytes.sub buf 0 recvd in
            (Printf.eprintf "received '%s' from %d\n%!" (escaped (Bytes.to_string msg)) fromport;
            loop (process_step (Incoming (msg, fromport)) state))
      with Unix.Unix_error (Unix.EAGAIN, "recvfrom", _) ->
        Printf.eprintf "Timed out\n%!";
        loop (process_step Timeout state)
  and
    read_file state =
    let buf = Bytes.create data_len in
    let rec read_helper already_read =
      let read = Unix.read filefd buf already_read (data_len - already_read) in
      if read < 0 then
        fail "IO error"
      else if (already_read + read) == data_len || read == 0 then (* read a full block or got EOF *)
        loop (process_step (Read (Bytes.sub buf 0 (already_read + read))) state)
      else
        read_helper (already_read + read)
    in
    read_helper 0
  and
    loop (actions, state) =
    (* actions are reversed because they're appended to front on Coq side*)
    let want_to_read = map handle_action (List.rev actions) in
    if List.mem true want_to_read then (* if any action made us want to read from file *)
      read_file state
    else (* otherwise go by default - wait for packets on the network *)
      receive state
  in
  loop (initialize_connection tid port)
