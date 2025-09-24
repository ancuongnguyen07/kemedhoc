module Impl.KEMEDHOC.Core.Msg3

module HACLRandom = Lib.RandomSequence

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module Spec = Spec.KEMEDHOC.Core

module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecParser = Spec.KEMEDHOC.Parser
module SpecTH = Spec.KEMEDHOC.TranscriptHash
module SpecKS = Spec.KEMEDHOC.KeySchedule

module SpecEdhocSerd = Spec.EDHOC.Serialization

module TypeEdhoc = TypeHelper.EDHOC

#push-options "--z3refresh --z3rlimit 70 --max_fuel 2 --max_ifuel 1"

(*------------------ Responder's side*)
let responder_process_msg3 kcs rs hs p2 msg3 p3
  = (**) let h0 = ST.get() in

  (**) assert(is_valid_handshake_state_m h0 hs);
  let res = responder_process_msg3_decrypt_msg3 #kcs rs hs p2 msg3 p3 in
  (**) let h_final = ST.get() in
  (**) assume(
    res <> TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
    ==> (
      let res_s = Spec.responder_process_msg3 kcs (party_state_m_eval h0 rs)
                  (handshake_state_m_eval h0 hs)
                  (plaintext2_eval h0 p2)
                  (as_seq h0 msg3) in

      match res_s with
        | Fail e -> res == error_to_c_response e
        | Res (hs_s, p3_s) -> (
          let hs_s_final = handshake_state_m_eval h_final hs in
          let p3_s_final = plaintext3_eval h_final p3 in

          res == TypeEdhoc.CSuccess
          /\ Spec.is_valid_handshake_state_after_msg3 hs_s_final
          /\ Spec.hs_equal hs_s hs_s_final
          /\ SpecParser.plaintext3_equal p3_s_final p3_s
        )
    )
  );
  res

(*------------------ Initiator's side*)
let initiator_send_msg3 kcs is hs p2 msg3
  = (**) let h0 = ST.get() in

  initiator_send_msg3_set_up #kcs is hs p2;
  let final_res = initiator_send_msg3_construct_msg3 #kcs is hs msg3 in


  (**) let h_final = ST.get() in
  (**) assume(
    final_res <> TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
    ==> (let res_s = Spec.initiator_send_msg3 kcs (party_state_m_eval h0 is)
                  (handshake_state_m_eval h0 hs)
                  (plaintext2_eval h0 p2) in

      match res_s with
        | Fail e -> final_res == error_to_c_response e
        | Res (msg3_s, hs_s) -> (
          let hs_s_final = handshake_state_m_eval h_final hs in
          let msg3_s_final = as_seq h_final msg3 in

          final_res == TypeEdhoc.CSuccess
          /\ Spec.is_valid_handshake_state_after_msg3 hs_s_final
          /\ Spec.hs_equal hs_s_final hs_s
          /\ Seq.equal msg3_s_final msg3_s
        )
    )
  );
  final_res

#pop-options