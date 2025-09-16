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
#push-options "--z3refresh --z3rlimit 40 --max_fuel 4 --max_ifuel 4"
let responder_process_msg1 kcs rs msg1 hs
  = (**) let h0 = ST.get () in
  ST.push_frame();
  responder_process_msg1_set_up kcs rs msg1 hs;
  // decrypt ciphertext1 -> get plaintext1
  // let ptx1_buffer = create (plaintext1_size_t kcs) (u8 0) in
  // let res = decrypt_ciphertext1 #kcs msg1.c1 hs.th1 hs.prk1e ptx1_buffer in
  // let final_res = match res with
  //   | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
  //   | TypeEdhoc.CDecryptionFailure -> res
  //   | TypeEdhoc.CSuccess -> (
  //     // compute hash of message1
  //     let msg1_concat_len = concat_msg1_fixed_length_t kcs in
  //     let msg1_concat_buffer = create msg1_concat_len (u8 0) in
  //     (**) assert(message1_disjoint_to_lbuffer msg1 msg1_concat_buffer);
  //     do_hash kcs hs.msg1_hash msg1_concat_len msg1_concat_buffer;
  //     (**) let h5 = ST.get () in
  //     (**) assert(modifies (loc hs.k_auth_R |+| loc hs.th1 |+| loc hs.prk1e
  //           |+| loc ptx1_buffer
  //           |+| loc hs.msg1_hash
  //     ) h0 h5);

  //     res

  //   ) in

  ST.pop_frame();
  TypeEdhoc.CSuccess

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