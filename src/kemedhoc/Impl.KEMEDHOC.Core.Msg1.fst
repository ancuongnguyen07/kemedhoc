module Impl.KEMEDHOC.Core.Msg1

(*HACL Random lib*)
open Lib.RandomBuffer.System

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

module FBytes = FStar.Bytes

(*Specification modules*)
module Spec = Spec.KEMEDHOC.Core
friend Spec.KEMEDHOC.Core

module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecParser = Spec.KEMEDHOC.Parser

module TypeEdhoc = TypeHelper.EDHOC
module SpecEdhocSerd = Spec.EDHOC.Serialization

open Impl.KEMEDHOC.Core.Msg1.Aux

/// Responder's side
#push-options "--z3refresh --z3rlimit 45 --max_fuel 4 --max_ifuel 4"
let responder_process_msg1 kcs rs msg1 hs ptx1
  = (**) let h0 = ST.get () in
  ST.push_frame();
  responder_process_msg1_set_up kcs rs msg1 hs;
  let final_res = responder_process_msg1_decrypt_c1_get_ptx1 kcs rs msg1 hs ptx1 in

  ST.pop_frame();
  (**) let h_final = ST.get () in
  (**) assume(
    let res_s = Spec.responder_process_msg1 kcs (party_state_m_eval h0 rs)
                (message1_eval h0 msg1) in

    let hs_s_final = handshake_state_m_eval h_final hs in
    let ptx1_s_final = plaintext1_eval h_final ptx1 in

    (match res_s with
      | Fail e -> final_res == error_to_c_response e
      | Res (hs_s, p1_s) -> (
        final_res == TypeEdhoc.CSuccess /\
        Spec.hs_equal hs_s_final hs_s /\
        SpecParser.plaintext1_equal ptx1_s_final p1_s
      )
    )
  );
  final_res

#pop-options


/// Initiator's side
#push-options "--z3refresh --z3rlimit 50 --max_fuel 4 --max_ifuel 4"
let initiator_send_msg1 kcs is msg1 hs
  = (**) let h0 = ST.get () in
  ST.push_frame();

  initiator_set_up_msg1 kcs is hs msg1;
  let final_res = initiator_construct_msg1 kcs is hs msg1 in

  ST.pop_frame();
  (**) let h_final = ST.get () in
  (**) assert( final_res == TypeEdhoc.CSuccess ==> (
    is_valid_handshake_state_m h_final hs
    /\ is_valid_party_state_m h_final is
    /\ is_valid_message1 h_final msg1 /\ is_legit_message1 h_final msg1)
  );
  assume(
    let is_init = party_state_m_eval h0 is in
    let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in

    match (Spec.initiator_send_msg1 kcs is_init e0_v) with
      | Fail _ -> False
      | Res (msg1_spec, is_spec, hs_spec) -> (
        final_res == TypeEdhoc.CSuccess ==> (
          Spec.hs_equal (handshake_state_m_eval h_final hs) hs_spec
          /\ Spec.ps_equal_all (party_state_m_eval h_final is) is_spec
          /\ SpecParser.message1_equal (message1_eval h_final msg1) msg1_spec
        )
      )
  );
  final_res

#pop-options