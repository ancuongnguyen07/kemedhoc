module Impl.KEMEDHOC.Core.Msg2

(*LowStar related modules*)
open Lib.ByteBuffer
open Lib.IntTypes
open Lib.Buffer

(*HACL Random lib*)
open Lib.RandomBuffer.System
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

(*EDHOC utilities*)
open Impl.EDHOC.Utilities

(*KEMEDHOC utilities*)
open Impl.KEMEDHOC.Types
open Impl.KEMEDHOC.CryptoPrimitives
open Impl.KEMEDHOC.KeySchedule
open Impl.KEMEDHOC.Parser
open Impl.KEMEDHOC.Ciphertext
open Impl.KEMEDHOC.TranscriptHash
open Impl.KEMEDHOC.Core
open Spec.KEMEDHOC.Base.Definitions

open Impl.KEMEDHOC.Core.Msg2.Aux

(*------------------ Responder's side*)
val responder_send_msg2:
  kcs: supportedKemCipherSuite
  -> rs: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> msg1: message1 kcs
  -> msg2: message2 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_party_state_eph_est_m h0 rs
    /\ is_valid_message1 h0 msg1 /\ is_legit_message1 h0 msg1
    /\ is_valid_message2 h0 msg2
    /\ live h0 entropy_p /\ live h0 kem_state

    /\ (let hs_init = handshake_state_m_eval h0 hs in
      Spec.is_valid_handshake_state_init hs_init
    )

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs rs
    /\ handshake_state_m_disjoint_to_msg1 hs msg1
    /\ handshake_state_m_disjoint_to_msg2 hs msg2
    /\ handshake_state_m_disjoint_to_lbuffer hs entropy_p
    /\ handshake_state_m_disjoint_to_lbuffer hs kem_state
    /\ party_state_disjoint_to_msg1 rs msg1
    /\ party_state_disjoint_to_msg2 rs msg2
    /\ party_state_disjoint_to_lbuffer rs entropy_p
    /\ party_state_disjoint_to_lbuffer rs kem_state
    /\ message2_disjoint_to_msg1 msg2 msg1
    /\ message2_disjoint_to_lbuffer msg2 entropy_p
    /\ message2_disjoint_to_lbuffer msg2 kem_state
    /\ message1_disjoint_to_lbuffer msg1 entropy_p
    /\ message1_disjoint_to_lbuffer msg1 kem_state
    /\ disjoint kem_state entropy_p
  )
  (ensures fun h0 res h1 ->
    
    let modified_locs = loc kem_state |+| loc entropy_p
              |+| lbufferOpt_loc hs.k_xy |+| loc msg2.ct_y
              |+| lbufferOpt_loc hs.k_auth_I |+| loc msg2.ct_auth_I
              |+| lbufferOpt_loc hs.th2
              |+| lbufferOpt_loc hs.prk2e |+| lbufferOpt_loc hs.prk3e2m in 

    // memory modification post-condition
    (match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies modified_locs h0 h1
      | TypeEdhoc.CSuccess -> modifies (modified_locs |+| loc msg2.c2) h0 h1
      | _ -> False)
    // validity of management states and messages
    /\ (is_valid_handshake_state_m h1 hs
      /\ Spec.is_valid_handshake_state_after_msg2 (handshake_state_m_eval h1 hs)
      /\ is_valid_party_state_m h1 rs
      /\ is_valid_message2 h1 msg2
    )
    // functional correctness respect to the high-level specification
    // The error CUnsupportedAlgorithmOrInvalidConfig is implementation-specific
    // so it is not covered by the specification
    /\ ( res <> TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
      ==> (
      let rs_init = party_state_m_eval h0 rs in
      let hs_init = handshake_state_m_eval h0 hs in
      let msg1_init = message1_eval h0 msg1 in
      let entr = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in

      let res_s = Spec.responder_send_msg2 kcs rs_init hs_init msg1_init entr in

      let hs_s_final = handshake_state_m_eval h1 hs in
      let msg2_s_final = message2_eval h1 msg2 in

      match res_s with
        | Fail e -> res == error_to_c_response e
        | Res (m2_s, hs_s) -> (
          res == TypeEdhoc.CSuccess
          /\ Spec.hs_equal hs_s_final hs_s
          /\ SpecParser.message2_equal msg2_s_final m2_s
        )
    ))
  )


(*-------------------- Initiator's side*)
val initiator_process_msg2:
  kcs: supportedKemCipherSuite
  -> is: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> msg2: message2 kcs
  -> p2: plaintext2 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_party_state_eph_est_m h0 is
    /\ is_valid_message2 h0 msg2
    /\ is_valid_plaintext2 h0 p2

    /\ (let hs_init = handshake_state_m_eval h0 hs in
      Spec.is_valid_handshake_state_init hs_init
    )

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_msg2 hs msg2
    /\ handshake_state_m_disjoint_to_p2 hs p2
    /\ party_state_disjoint_to_msg2 is msg2
    /\ party_state_disjoint_to_p2 is p2
    /\ message2_disjoint_to_p2 msg2 p2
  )
  (ensures fun h0 res h1 ->
    let base_modified_locs = lbufferOpt_loc hs.k_xy |+| lbufferOpt_loc hs.k_auth_I
              |+| lbufferOpt_loc hs.th2 |+| lbufferOpt_loc hs.prk2e in

    // memory modification post-condition
    (match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
      | TypeEdhoc.CDecryptionFailure -> modifies base_modified_locs h0 h1
      | TypeEdhoc.CInvalidCredential
      | TypeEdhoc.CIntegrityCheckFailed
      | TypeEdhoc.CSuccess -> modifies (base_modified_locs |+| lbufferOpt_loc hs.prk3e2m
                                      |+| plaintext2_union p2) h0 h1
      | _ -> False
    )
    // validity of management states and messages
    /\ (is_valid_handshake_state_m h1 hs
      /\ (res == TypeEdhoc.CSuccess ==> Spec.is_valid_handshake_state_after_msg2 (handshake_state_m_eval h1 hs))
      /\ is_valid_party_state_m h1 is
      /\ is_valid_plaintext2 h1 p2
    )
    // functional correctness respect to the high-level specification
    // The error CUnsupportedAlgorithmOrInvalidConfig is implementation-specific
    // so it is not covered by the specification
    /\ (res <> TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
    ==> (
      let rs_init = party_state_m_eval h0 is in
      let hs_init = handshake_state_m_eval h0 hs in
      let msg2_init = message2_eval h0 msg2 in

      let res_s = Spec.initiator_process_msg2 kcs rs_init hs_init msg2_init in
      let hs_s_final = handshake_state_m_eval h1 hs in

      match res_s with
        | Fail e -> error_to_c_response e == res
        | Res (hs_s, p2_s) -> (
          res == TypeEdhoc.CSuccess
          /\ Spec.hs_equal hs_s_final hs_s
          /\ SpecParser.plaintext2_equal (plaintext2_eval h1 p2) p2_s
        )
    ))
  )
