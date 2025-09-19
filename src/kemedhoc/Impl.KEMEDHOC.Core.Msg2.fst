module Impl.KEMEDHOC.Core.Msg2


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


(*------------------ Responder's side*)
#push-options "--z3refresh --z3rlimit 60 --max_fuel 4 --max_ifuel 4"

let responder_send_msg2 kcs rs hs msg1 msg2
  = (**) let h0 = ST.get () in
  responder_send_msg2_set_up kcs rs hs msg1 msg2;
  let res = responder_construct_msg2 kcs rs hs msg2 in

  (**) let h_final = ST.get () in
  (**) assert(
    lbufferOpt_is_Some h_final hs.k_xy /\ lbufferOpt_is_Some h_final hs.k_auth_I
    /\ lbufferOpt_is_Some h_final hs.th2 /\ lbufferOpt_is_Some h_final hs.prk2e
    /\ lbufferOpt_is_Some h_final hs.prk3e2m
  );
  (**) assume(
    res <> TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
    ==> (
    let rs_init = party_state_m_eval h0 rs in
    let hs_init = handshake_state_m_eval h0 hs in
    let msg1_init = message1_eval h0 msg1 in
    let entr = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in

    let res_s = Spec.responder_send_msg2 kcs rs_init hs_init msg1_init entr in

    let hs_s_final = handshake_state_m_eval h_final hs in
    let msg2_s_final = message2_eval h_final msg2 in

    match res_s with
      | Fail e -> res == error_to_c_response e
      | Res (m2_s, hs_s) -> (
        res == TypeEdhoc.CSuccess
        /\ Spec.hs_equal hs_s_final hs_s
        /\ SpecParser.message2_equal msg2_s_final m2_s
      )
    ));
    res

(*------------------ Initiator's side*)
let initiator_process_msg2 kcs is hs msg2 p2
  = (**) let h0 = ST.get () in
  initiator_process_msg2_set_up kcs is hs msg2;
  let res = initiator_process_msg2_decrypt_c2 kcs is hs msg2 p2 in

  (**) let h_final = ST.get () in
  (**) assert(
    lbufferOpt_is_Some h_final hs.k_xy /\ lbufferOpt_is_Some h_final hs.k_auth_I
    /\ lbufferOpt_is_Some h_final hs.th2 /\ lbufferOpt_is_Some h_final hs.prk2e
    /\ (res == TypeEdhoc.CSuccess ==> lbufferOpt_is_Some h_final hs.prk3e2m)
  );
  (**) assume(
    res <> TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
    ==> (
      let rs_init = party_state_m_eval h0 is in
      let hs_init = handshake_state_m_eval h0 hs in
      let msg2_init = message2_eval h0 msg2 in

      let res_s = Spec.initiator_process_msg2 kcs rs_init hs_init msg2_init in
      let hs_s_final = handshake_state_m_eval h_final hs in

      match res_s with
        | Fail e -> error_to_c_response e == res
        | Res (hs_s, p2_s) -> (
          res == TypeEdhoc.CSuccess
          /\ Spec.hs_equal hs_s_final hs_s
          /\ SpecParser.plaintext2_equal (plaintext2_eval h_final p2) p2_s
        )
    )
  );
  res

#pop-options

