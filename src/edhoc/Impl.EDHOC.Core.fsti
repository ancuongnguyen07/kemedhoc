module Impl.EDHOC.Core

(*HACL related modules*)
// open Lib.RawIntTypes
open Lib.IntTypes
// open Lib.Sequence
open Lib.ByteBuffer
// lbuffer type, an immutable buffer with
// length tag, is from this module
// let lbuffer (a:Type0) (len:size_t) = lbuffer_t MUT a len
// `live` and `disjoint` are also from this module.
// Basically, HACL `Lib.Buffer` is a wrapper of `LowStar.Buffer`
// and related LowStar memory models.
open Lib.Buffer
open Lib.RandomBuffer.System

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

module Spec = Spec.EDHOC.Core
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecSerd = Spec.EDHOC.Serialization
module SpecParser = Spec.EDHOC.Parser
module SpecCoreLemma = Spec.EDHOC.Core.Lemmas

open Spec.EDHOC.Base.Definitions

open Impl.EDHOC.CryptoPrimitives
open Impl.EDHOC.KeySchedule
open Impl.EDHOC.Ciphertext
open Impl.EDHOC.TranscriptHash
open Impl.EDHOC.Parser
open Impl.EDHOC.Utilities
open Impl.EDHOC.Core.Types
open TypeHelper.EDHOC

module HACLRandom = Lib.RandomSequence


(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)
val responder_process_msg1:
  #cs:SpecCrypto.supported_cipherSuite
  -> rs_m:party_state_mem_shared_est #cs
  -> msg1_m:message1_mem #cs
  -> msg1_len:size_t{msg1_len = message1_mem_get_length msg1_m}
  -> hs_m:hs_mem_after_msg1 #cs
  -> ST.Stack c_response
  (requires fun h0 -> is_valid_party_state_mem h0 rs_m /\ is_valid_hs_mem h0 hs_m
    /\ is_legit_party_state_mem h0 rs_m /\ is_valid_message1_mem_after_init h0 msg1_m
    // disjoint clauses. Cannot use B.all_disjoint as Z3 solver could not
    // unfold further disjoint clauses ---> making even trivial proofs failed
    /\ hs_mem_disjoint_to_msg1_m hs_m msg1_m /\ hs_mem_disjoint_to_ps_mem hs_m rs_m
    /\ party_state_mem_disjoint_to_msg1_m rs_m msg1_m
  )
  (ensures fun h0 cres h1 -> (
    let msg1_h0_abstract = eval_message1_mem h0 msg1_m in
    let rs_h0_abstract = eval_party_state_mem h0 rs_m in
    SpecCoreLemma.lemma_responder_process_msg1_agreement #cs rs_h0_abstract msg1_h0_abstract;
    let res_abstract = Spec.responder_process_msg1 #cs rs_h0_abstract msg1_h0_abstract in

    (cres == CSuccess \/ cres == CUnsupportedCipherSuite)
    /\ (match res_abstract with
        | Fail e -> cres == error_to_c_response e
        | Res _ -> cres == CSuccess
    )
    /\ (match cres with
        | CSuccess -> Res? res_abstract
        | CUnsupportedCipherSuite ->
          res_abstract == Fail UnsupportedCipherSuite
          /\ modifies0 h0 h1
    )
    /\ (cres == CSuccess ==> (
      let modified_loc = loc hs_m.method |+| loc hs_m.suite_i
                      |+| loc hs_m.g_x |+| loc hs_m.msg1_hash in

      modifies modified_loc h0 h1
      /\ is_legit_party_state_mem h1 rs_m
      /\ is_legit_hs_mem h1 hs_m
      /\ (
        let hs_r_h1_abstract = eval_hs_mem h1 hs_m in
        let hs_r_spec = match res_abstract with Res hs -> hs in

        Spec.hs_equal_after_msg1 hs_r_h1_abstract hs_r_spec
      )
    ))
  ))

(*-------------------------------------------*)
(*---------------------------- Initiator side*)
(*-------------------------------------------*)
val initiator_send_msg1:
  cs:SpecCrypto.supported_cipherSuite
  -> method_l:method_label
  -> msg1_m:message1_mem #cs
  -> msg1_m_len:size_t{msg1_m_len = message1_mem_get_length msg1_m
    /\ size_v msg1_m_len <= SpecCrypto.alg_get_hash_max_input (SpecCrypto.get_hash_alg cs)
  }
  -> is_m:party_state_mem #cs
  -> hs_i_m:hs_mem #cs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_message1_mem h0 msg1_m /\ is_valid_party_state_mem h0 is_m
    /\ is_legit_party_state_mem h0 is_m
    /\ is_valid_hs_mem h0 hs_i_m /\ live h0 entropy_p
    // requires neccessarily not-null fields
    /\ ~(g_is_null_ps_eph_keypair is_m)
    /\ (
      ~(g_is_null hs_i_m.g_x) /\ ~(g_is_null hs_i_m.msg1_hash)
      // it is assumed that the EAD1 buffer is explicit NULL
      // or be constrained with the length = 0
    )
    /\ party_state_mem_disjoint_to is_m entropy_p
    /\ party_state_mem_disjoint_to_msg1_m is_m msg1_m
    /\ hs_mem_disjoint_to hs_i_m entropy_p /\ message1_mem_disjoint_to msg1_m entropy_p
    /\ hs_mem_disjoint_to_ps_mem hs_i_m is_m /\ hs_mem_disjoint_to_msg1_m hs_i_m msg1_m

  )
  (ensures fun h0 cres h1 -> (
    let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
    let modified_is_loc = opt_ec_keypair_mem_union_loc (party_state_mem_get_shared_key is_m) in
    let is_h0_abstract = eval_party_state_mem h0 is_m in
    let method_e = label_to_method method_l in
    SpecCoreLemma.lemma_initiator_send_msg1_responds cs method_e e0_v is_h0_abstract;
    let res_abstract = (Spec.initiator_send_msg1 cs method_e e0_v is_h0_abstract) in

    (cres == CSuccess \/ cres == CInvalidECPoint)
    /\ (match res_abstract with
        | Res (msg1_ab, is_shared_est, hs_i_after_msg1_ab) -> cres == CSuccess
        | Fail InvalidECPoint -> cres == CInvalidECPoint
        | Fail _ -> False
    )
    /\ (match cres with
        | CSuccess -> Res? res_abstract
        | CInvalidECPoint ->
          res_abstract == Fail InvalidECPoint
          /\ modifies (modified_is_loc |+| loc entropy_p) h0 h1
    )
    
    /\ (cres == CSuccess ==> (
      (
        let modified_hs_loc = loc hs_i_m.msg1_hash |+| loc hs_i_m.suite_i
                            |+| loc hs_i_m.method |+| loc hs_i_m.g_x in
        let modified_loc = (message1_mem_union_loc_non_ead1 msg1_m) |+| loc entropy_p
                          |+| modified_hs_loc |+| modified_is_loc in
        modifies modified_loc h0 h1
      )
      /\ is_legit_hs_mem h1 hs_i_m
      /\ is_valid_message1_mem_after_init h1 msg1_m
      /\ is_legit_party_state_mem h1 is_m
      /\ (
        // get entropies at different memory snapshots. Used for proofs only
        let e1_v = B.deref h1 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in

        let is_h1_abstract = eval_party_state_mem h1 is_m in
        let hs_i_h1_abstract = eval_hs_mem h1 hs_i_m in
        let msg1_m_abstract = eval_message1_mem h1 msg1_m in

        match res_abstract with
          | Fail e -> False
          | Res (msg1_ab, is_shared_est, hs_i_after_msg1_ab) -> (

            SpecParser.message1_compare msg1_ab msg1_m_abstract
            /\ Seq.equal msg1_m_abstract.g_x hs_i_h1_abstract.g_x
            /\ Spec.hs_equal_after_msg1 hs_i_h1_abstract hs_i_after_msg1_ab
            /\ Spec.ps_equal is_shared_est is_h1_abstract
          )
      )
    ))
  ))
