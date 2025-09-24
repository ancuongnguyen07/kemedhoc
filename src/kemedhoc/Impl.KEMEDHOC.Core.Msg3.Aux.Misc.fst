module Impl.KEMEDHOC.Core.Msg3.Aux.Misc

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

module FBytes = FStar.Bytes

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
open Impl.KEMEDHOC.Core.Utilities
open Impl.KEMEDHOC.Core.Msg3.Aux
open Spec.KEMEDHOC.Base.Definitions

module AuxMsg2 = Impl.KEMEDHOC.Core.Msg2.Aux

val responder_process_msg3_decrypt_msg3:
  #kcs: supportedKemCipherSuite
  -> rs: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> p2: plaintext2 kcs
  -> msg3: message3 kcs
  -> p3: plaintext3 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_party_state_eph_est_m h0 rs
    /\ is_valid_handshake_state_m h0 hs
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

    match res with
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
        /\ lbufferOpt_is_Some h1 hs.th3 /\ lbufferOpt_is_Some h1 hs.prk4e3m
        /\ lbufferOpt_is_Some h1 hs.th4 /\ lbufferOpt_is_Some h1 hs.prk_out
        /\ lbufferOpt_is_Some h1 hs.prk_exporter
      )
      | _ -> False
  )

#push-options "--z3refresh --z3rlimit 150 --fuel 2 --ifuel 1"

let responder_process_msg3_decrypt_msg3 #kcs rs hs p2 msg3 p3
  = (**) let h0 = ST.get () in
  ST.push_frame();

  // derive TH3
  let cred_R = create (size SpecParser.cred_size) (u8 0) in
  copy cred_R rs.id_cred;
  compute_th3 #kcs hs.th2.value p2 cred_R hs.th3.value;
  lbufferOpt_set_Some hs.th3; // set TH3 as Some
  (**) let h1 = ST.get () in
  (**) assert(is_valid_handshake_state_m h1 hs);

  // create plaintext3
  let p3_buffer = create (plaintext3_size_t kcs) (u8 0) in

  // decrypt ciphertext3
  let res = decrypt_ciphertext3 #kcs msg3 hs.th3.value hs.prk3e2m.value p3_buffer in
  (**) let h1_1 = ST.get () in

  let final_res = match res with
    | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> (
      (**) let h2_1 = ST.get () in
      (**) assert(modifies0 h1_1 h2_1);
      
      TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
    )
    | TypeEdhoc.CDecryptionFailure -> (
      (**) let h2_1 = ST.get () in
      (**) assert(modifies0 h1_1 h2_1);

      TypeEdhoc.CDecryptionFailure
    )
    | TypeEdhoc.CSuccess -> (
      (**) let h2_1 = ST.get () in
      (**) assert(is_valid_handshake_state_m h2_1 hs);

      // deserialize plaintext3
      deserialize_ptx3 kcs p3_buffer p3;
      (**) let h2 = ST.get () in
      (**) assert(
        modifies (plaintext3_union p3) h1_1 h2
      );

      // process plaintext3
      let res_process = responder_process_msg3_decrypt_msg3_uti #kcs rs hs p3 in
      (**) let h3 = ST.get () in
      (**) assert(
        let base_modified_locs = lbufferOpt_loc hs.prk4e3m
                      |+| plaintext3_union p3 in

        match res_process with
          | TypeEdhoc.CIntegrityCheckFailed -> (

            modifies base_modified_locs h2_1 h3
            /\ lbufferOpt_is_Some h3 hs.prk4e3m
          )
          | TypeEdhoc.CSuccess -> (
            let modified_locs = base_modified_locs
                |+| lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
                |+| lbufferOpt_loc hs.prk_exporter in

            modifies modified_locs h2_1 h3
            /\ lbufferOpt_is_Some h3 hs.prk4e3m
            /\ lbufferOpt_is_Some h3 hs.th4 /\ lbufferOpt_is_Some h3 hs.prk_out
            /\ lbufferOpt_is_Some h3 hs.prk_exporter
          )
          | _ -> False
      );


      res_process
    ) in

  ST.pop_frame();
  (**) let h_final = ST.get () in
  (**) assert(
    let base_modified_locs = lbufferOpt_loc hs.th3 in

    match final_res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
      | TypeEdhoc.CDecryptionFailure -> (
        modifies base_modified_locs h0 h_final
        /\ lbufferOpt_is_Some h_final hs.th3
      )
      | TypeEdhoc.CIntegrityCheckFailed -> (
        let modified_locs = base_modified_locs |+| lbufferOpt_loc hs.prk4e3m
                         |+| plaintext3_union p3 in

        modifies modified_locs h0 h_final
        /\ lbufferOpt_is_Some h_final hs.th3 /\ lbufferOpt_is_Some h_final hs.prk4e3m
      )
      | TypeEdhoc.CSuccess -> (
        let modified_locs = base_modified_locs
                |+| lbufferOpt_loc hs.prk4e3m
                |+| plaintext3_union p3
                |+| lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
                |+| lbufferOpt_loc hs.prk_exporter in

        modifies modified_locs h0 h_final
        /\ lbufferOpt_is_Some h_final hs.th3 /\ lbufferOpt_is_Some h_final hs.prk4e3m
        /\ lbufferOpt_is_Some h_final hs.th4 /\ lbufferOpt_is_Some h_final hs.prk_out
        /\ lbufferOpt_is_Some h_final hs.prk_exporter
      )
      | _ -> False
  );
  final_res

#pop-options