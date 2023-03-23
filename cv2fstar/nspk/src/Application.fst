module Application

open CVTypes
friend CVTypes
open NSL.Types
friend NSL.Types
open State
open NSL.Functions
open NSL.Tables
open NSL.Sessions
open NSL.Events
open NSL.Protocol
open NSL.Initiator
open NSL.Responder
open NSL.Setup
open NSL.Key_Register

// These are only needed for the definition of addrA and addrB
open Lib.IntTypes
open Lib.ByteSequence

// generated: "A@localhost"
inline_for_extraction
let size_addrA:size_nat = 11
let addrA_list:l: list uint8 {List.Tot.length l == size_addrA} =
  [@@ inline_let ]let l =
    [
      u8 0x41; u8 0x40; u8 0x6c; u8 0x6f; u8 0x63; u8 0x61; u8 0x6c; u8 0x68; u8 0x6f; u8 0x73;
      u8 0x74
    ]
  in
  assert_norm (List.Tot.length l == size_addrA);
  l
let addrA:lbytes size_addrA = Seq.createL addrA_list

// generated: "B@localhost"
inline_for_extraction
let size_addrB:size_nat = 11
let addrB_list:l: list uint8 {List.Tot.length l == size_addrB} =
  [@@ inline_let ]let l =
    [
      u8 0x42; u8 0x40; u8 0x6c; u8 0x6f; u8 0x63; u8 0x61; u8 0x6c; u8 0x68; u8 0x6f; u8 0x73;
      u8 0x74
    ]
  in
  assert_norm (List.Tot.length l == size_addrB);
  l
let addrB:lbytes size_addrB = Seq.createL addrB_list

(* This is manually written code, it is only implicit in the CryptoVerif model. *)
val add_honest_parties: nsl_state -> Tot (nsl_state * bool)
let add_honest_parties st =
  match oracle_setup st addrA with
  | st, None -> st, false
  | st, Some pkA ->
    match oracle_setup st addrB with
    | st, None -> st, false
    | st, Some pkB -> st, true

val initialize: Lib.RandomSequence.entropy -> Tot (nsl_state * bool)
let initialize ent =
  let st = init_state nsl_state_type ent in
  add_honest_parties st

val testrun: Lib.RandomSequence.entropy -> FStar.All.ML Lib.RandomSequence.entropy
let testrun ent =
  match initialize ent with
  | st0, false ->
    IO.print_string "fail";
    finalize_state st0
  | st0, true ->
    IO.print_string "## Tables After Calling Setup\n\n";
    nsl_print_tables st0;
    IO.print_string "\n";
    match oracle_initiator__send__msg__1 st0 addrA addrB with
    | st1, None ->
      IO.print_string "init_send_1 fail";
      finalize_state st1
    | st1, Some (id_init, c1) ->
      IO.print_string "## Sessions After init_send_msg_1\n\n";
      nsl_print_session st1 id_init;
      IO.print_string "\n\n";
      IO.print_string "## Protocol Message 1\n\n";
      print_label_bytes "ct" (serialize_ciphertext c1) true;
      IO.print_string "\n\n";
      match oracle_responder__send__msg__2 st1 addrB c1 with
      | st2, None ->
        nsl_print_session st2 id_init;
        IO.print_string "resp_send_2 fail";
        finalize_state st2
      | st2, Some (id_resp, c2) ->
        IO.print_string "## Sessions After resp_send_msg_2\n\n";
        nsl_print_session st2 id_init;
        nsl_print_session st2 id_resp;
        IO.print_string "\n\n";
        IO.print_string "## Protocol Message 2\n\n";
        print_label_bytes "ct" (serialize_ciphertext c2) true;
        IO.print_string "\n\n";
        match oracle_initiator__send__msg__3 st2 id_init c2 with
        | st3, None ->
          nsl_print_session st3 id_init;
          IO.print_string "init_send_3 fail";
          finalize_state st3
        | st3, Some c3 ->
          IO.print_string "## Sessions After init_send_msg_3\n\n";
          nsl_print_session st3 id_init;
          nsl_print_session st3 id_resp;
          IO.print_string "\n\n";
          IO.print_string "## Protocol Message 3\n\n";
          print_label_bytes "ct" (serialize_ciphertext c3) true;
          IO.print_string "\n\n";
          match oracle_responder__receive__msg__3 st3 id_resp c3 with
          | st4, None ->
            nsl_print_session st4 id_resp;
            IO.print_string "resp_recv_3 fail";
            finalize_state st4
          | st4, Some () ->
            IO.print_string "## Sessions After resp_recv_msg_3\n\n";
            nsl_print_session st4 id_init;
            nsl_print_session st4 id_resp;
            IO.print_string "\n\n";
            match oracle_initiator__finish st4 id_init with
            | st5, None ->
              IO.print_string "initiator_finish fail";
              finalize_state st5
            | st5, Some () ->
              IO.print_string "## Sessions After init_finish\n\n";
              nsl_print_session st5 id_init;
              nsl_print_session st5 id_resp;
              IO.print_string "\n\n";
              IO.print_string "## Event List at the End of Protocol Execution\n\n";
              print_events st5 nsl_print_event;
              IO.print_string "\n\n";
              IO.print_string "success\n";
              finalize_state st5

let run =
  let entropy = testrun Lib.RandomSequence.entropy0 in
  ()

