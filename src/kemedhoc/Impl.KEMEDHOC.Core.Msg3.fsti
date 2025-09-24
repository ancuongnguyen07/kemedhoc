module Impl.KEMEDHOC.Core.Msg3

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

open Impl.KEMEDHOC.Core.Msg3.Aux
open Impl.KEMEDHOC.Core.Msg3.Aux.Misc
module AuxMsg2 = Impl.KEMEDHOC.Core.Msg2.Aux

(*------------------ Utilities*)

(*------------------ Responder's side*)
val responder_process_msg3:
  kcs: supportedKemCipherSuite
  -> rs: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> p2: plaintext2 kcs
  -> msg3: message3 kcs
  -> p3: plaintext3 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_party_state_eph_est_m h0 rs
    
    /\ is_valid_handshake_state_m h0 hs
    /\ is_valid_handshake_state_m_after_msg2 h0 hs
    /\ lbufferOpt_is_Some h0 hs.remote_id_cred

    /\ is_valid_plaintext2 h0 p2
    /\ is_valid_plaintext3 h0 p3
    /\ live h0 msg3

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs rs
    /\ AuxMsg2.handshake_state_m_disjoint_to_p2 hs p2
    /\ handshake_state_m_disjoint_to_lbuffer hs msg3
    /\ handshake_state_m_disjoint_to_p3 hs p3

    /\ AuxMsg2.party_state_disjoint_to_p2 rs p2
    /\ party_state_disjoint_to_p3 rs p3
    /\ party_state_disjoint_to_lbuffer rs msg3

    /\ plaintext2_disjoint_to_lbuffer p2 msg3

    /\ plaintext3_disjoint_to_plaintex2 p3 p2
    /\ plaintext3_disjoint_to_lbuffer p3 msg3
  )
  (ensures fun h0 res h1 ->
    let base_modified_locs = lbufferOpt_loc hs.th3 in

    is_party_state_eph_est_m h1 rs
    /\ is_valid_handshake_state_m h1 hs
    // Memory modification and validity of the handshake state
    /\ (match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
      | TypeEdhoc.CDecryptionFailure -> (
        modifies base_modified_locs h0 h1
        /\ lbufferOpt_is_Some h1 hs.th3
      )
      | TypeEdhoc.CIntegrityCheckFailed -> (
        let modified_locs = base_modified_locs |+| lbufferOpt_loc hs.prk4e3m
                          |+| plaintext3_union p3 in

        modifies modified_locs h0 h1
        /\ lbufferOpt_is_Some h1 hs.th3 /\ lbufferOpt_is_Some h1 hs.prk4e3m
      )
      | TypeEdhoc.CSuccess -> (
        let modified_locs = base_modified_locs
                |+| lbufferOpt_loc hs.prk4e3m
                |+| plaintext3_union p3
                |+| lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
                |+| lbufferOpt_loc hs.prk_exporter in

        modifies modified_locs h0 h1
        /\ is_valid_handshake_state_m_after_msg3 h1 hs
      )
      | _ -> False)
      // Functional correctness w.r.t. the high-level specification
      /\ (res <> TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
      ==> (let rs_init = party_state_m_eval h0 rs in
        let hs_init = handshake_state_m_eval h0 hs in
        let p2_init = plaintext2_eval h0 p2 in
        let msg3_init = as_seq h0 msg3 in

        let res_s = Spec.responder_process_msg3 kcs rs_init hs_init p2_init msg3_init in
        match res_s with
          | Fail e -> res == error_to_c_response e
          | Res (hs_s, p3_s) -> (
            let hs_final = handshake_state_m_eval h1 hs in

            res == TypeEdhoc.CSuccess
            /\ Spec.is_valid_handshake_state_after_msg3 hs_final
            /\ Spec.hs_equal hs_s hs_final
            /\ SpecParser.plaintext3_equal (plaintext3_eval h1 p3) p3_s
          )
      ))
  )

(*------------------ Initiator's side*)
val initiator_send_msg3:
  kcs: supportedKemCipherSuite
  -> is: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> p2: plaintext2 kcs
  -> msg3: message3 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_handshake_state_m_after_msg2 h0 hs
    /\ is_valid_party_state_m h0 is
    /\ is_party_state_eph_est_m h0 is
    /\ is_valid_plaintext2 h0 p2
    /\ live h0 msg3

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_lbuffer hs msg3
    /\ AuxMsg2.handshake_state_m_disjoint_to_p2 hs p2
    /\ AuxMsg2.party_state_disjoint_to_p2 is p2
    /\ party_state_disjoint_to_lbuffer is msg3
    /\ plaintext2_disjoint_to_lbuffer p2 msg3

  )
  (ensures fun h0 res h1 ->
    let base_modified_locs = lbufferOpt_loc hs.th3 |+| lbufferOpt_loc hs.prk4e3m in

    is_valid_party_state_m h1 is
    /\ is_party_state_eph_est_m h1 is
    /\ is_valid_handshake_state_m h1 hs
    // Memory modification and validity of the handshake state
    /\ (match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> (
        modifies base_modified_locs h0 h1
      )
      | TypeEdhoc.CSuccess -> (
        let modified_locs = base_modified_locs
                |+| lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
                |+| lbufferOpt_loc hs.prk_exporter
                |+| loc msg3 in

        modifies modified_locs h0 h1
        /\ is_valid_handshake_state_m_after_msg3 h1 hs
      )
      | _ -> False)
    // Functional correctness w.r.t. the high-level specification
    /\ (res <> TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
    ==> (let is_init = party_state_m_eval h0 is in
      let hs_init = handshake_state_m_eval h0 hs in
      let p2_init = plaintext2_eval h0 p2 in

      let res_s = Spec.initiator_send_msg3 kcs is_init hs_init p2_init in
      match res_s with
        | Fail e -> res == error_to_c_response e
        | Res (m3_s, hs_s) -> (
          let hs_final = handshake_state_m_eval h1 hs in

          res == TypeEdhoc.CSuccess
          /\ Spec.is_valid_handshake_state_after_msg3 hs_final
          /\ Spec.hs_equal hs_final hs_s 
          /\ Seq.equal (as_seq h1 msg3) m3_s
        )
    ))
  )