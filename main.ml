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
let fail message = Printf.printf "%s\n" message; exit 1

type transfer_direction = Upload of string | Download of string

let parse_args () =
  let ip = ref "" in
  let port = ref 69 in
  let upload = ref "" in
  let download = ref "" in
  Arg.parse [("-ip", Arg.Set_string ip, "IP address of server to connect to"); ("-port", Arg.Set_int port, "port of the server"); ("-download", Arg.Set_string download, "filename to download"); ("-upload", Arg.Set_string upload, "filename to upload")] (fun anon -> Printf.printf "Unrecognized argument: %s\n" anon; exit 1) "Simple TFTP client in OCaml and Coq";
  if !ip = "" then fail "IP not specified";
  if !upload = "" && !download = "" then fail "Provide a filename to download or upload";
  if !upload <> "" && !download <> "" then fail "You can either choose download or upload but not both";
  if !upload != "" then (!ip, !port, Upload !upload)
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
type action = Send of message * int | Terminate
type event = Incoming of message * int | Timeout (* TODO should also provide IP? *) (*TODO add terminated event*)

let translate_coq_result (coq_action, coq_state) : action * state =
  let action = match coq_action with
    | Coq_send (msg, port) -> Send (list_to_str msg, port)
    | Coq_terminate -> Terminate in
  (action, coq_state)

let initialize_connection (tid : int) (port : int) (transfer : transfer_direction) : action * state =
  let coq_transfer = match transfer with
    | Upload fname -> TFTP_Core.Coq_upload (str_to_list fname)
    | Download fname -> TFTP_Core.Coq_download (str_to_list fname)
  in
  translate_coq_result (TFTP_Core.initialize tid port coq_transfer)

let process_step (event :  event) (state : state) : action * state =
  let coq_event = match event with
    | Incoming (msg, sender) -> TFTP_Core.Coq_incoming (str_to_list msg, sender)
    | Timeout -> TFTP_Core.Coq_timeout in
  translate_coq_result (TFTP_Core.process_step coq_event state)

let max_packet_len = 600

let main =
  Random.self_init(); (* initialize randomness *)
  Printf.printf "hello world\n";
  let (ip, port, transfer) = parse_args() in
  let tid = assign_random_TID () in
  Printf.printf "Connecting to %s:%d, my tid is %d\n%!" ip port tid;
  let fd = create_udp_socket tid in
  let make_addr port = ADDR_INET ((inet_addr_of_string ip), port) in
  let rec loop (action, state) =
    match action with
    | Terminate -> Printf.printf "quitting\n"; exit 0
    | Send (msg, port) ->
      Printf.printf "sending '%s'\n%!" (Bytes.to_string msg);
      let toaddr = make_addr port in
      let sent = Unix.sendto fd msg 0 (Bytes.length msg) [] toaddr in
      if sent <> Bytes.length msg then Printf.printf "Warning: message has not been sent whole, shouldn't ever happen with UDP! Sent %d/%d bytes" sent (Bytes.length msg);
      Printf.printf "waiting for reply\n%!";
      let buf = Bytes.create max_packet_len in
      try
        let (recvd, sender) = Unix.recvfrom fd buf 0 max_packet_len [] in
        match sender with
        | ADDR_UNIX _ -> fail "Did not expect a UNIX message on UDP socket!"
        | ADDR_INET (fromip, fromport) ->
          if recvd <= 0 then (* TODO this is not a timeout but terminated conn *)
            (Printf.printf "Receive error\n%!";
            loop (process_step Timeout state))
          else
            (Printf.printf "received '%s'\n%!" (Bytes.to_string buf);
            loop (process_step (Incoming (Bytes.sub buf 0 recvd, fromport)) state))
      with Unix.Unix_error (Unix.EAGAIN, "recvfrom", _) ->
        Printf.printf "Timed out\n%!";
        loop (process_step Timeout state)
  in
  loop (initialize_connection tid port transfer)
