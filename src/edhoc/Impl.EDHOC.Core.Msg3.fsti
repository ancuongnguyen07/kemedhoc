module Impl.EDHOC.Core.Msg3

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
module SpecKS = Spec.EDHOC.KeySchedule

open Spec.EDHOC.Base.Definitions
open Spec.EDHOC.Core.Lemmas

open Impl.EDHOC.CryptoPrimitives
open Impl.EDHOC.KeySchedule
open Impl.EDHOC.Ciphertext
open Impl.EDHOC.TranscriptHash
open Impl.EDHOC.Parser
open Impl.EDHOC.Utilities
open Impl.EDHOC.Core.Types
open TypeHelper.EDHOC

open Impl.EDHOC.Core.Msg2.Aux
open Impl.EDHOC.Core.Msg3.Aux

module HACLRandom = Lib.RandomSequence

(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)
val responder_process_msg3:
  #cs:SpecCrypto.supported_cipherSuite
  -> #msg3_len:size_t
  -> method:method_enum
  -> rs_m:party_state_mem_shared_est #cs
  -> hs_m:hs_mem_after_msg2 #cs
  -> ptx2_m:plaintext2_mem #cs #(SpecCrypto.get_auth_material Responder method)
  -> msg3_buff:lbuffer uint8 msg3_len
  -> ST.Stack c_response
  (requires fun h0 -> live h0 entropy_p /\
    is_valid_hs_mem h0 hs_m /\ is_legit_hs_mem h0 hs_m
    /\ is_valid_party_state_mem h0 rs_m /\ is_legit_party_state_mem h0 rs_m
    /\ is_valid_plaintext2_mem h0 ptx2_m /\ live h0 msg3_buff
    /\ ( let tag_size_v = size (SpecCrypto.aead_tag_size (SpecCrypto.get_aead_alg cs)) in
      msg3_len = plaintext3_len_fixed_v cs (SpecCrypto.get_auth_material Initiator method)
        +! tag_size_v
    )
    // disjoint clauses
    /\ hs_mem_disjoint_to_ps_mem hs_m rs_m /\ hs_mem_disjoint_to hs_m entropy_p
    /\ hs_mem_disjoint_to_ptx2 hs_m ptx2_m /\ hs_mem_disjoint_to hs_m msg3_buff
    /\ ps_mem_disjoint_to_ptx2 rs_m ptx2_m /\ party_state_mem_disjoint_to rs_m msg3_buff
    /\ party_state_mem_disjoint_to rs_m entropy_p
    /\ plaintext2_mem_disjoint_to_buffer ptx2_m msg3_buff
    /\ plaintext2_mem_disjoint_to_buffer ptx2_m entropy_p
    /\ disjoint msg3_buff entropy_p
  )
  (ensures fun h0 cres h1 ->
    // True
    (cres == CSuccess \/ cres == CDecryptionFailure)
  )


(*-------------------------------------------*)
(*---------------------------- Initiator side*)
(*-------------------------------------------*)
val initiator_send_msg3:
  #cs:SpecCrypto.supported_cipherSuite
  -> #msg3_len:size_t
  -> method:method_enum
  -> is_m:party_state_mem_shared_est #cs
  -> hs_m:hs_mem_after_msg2 #cs
  -> ptx2_m:plaintext2_mem #cs #(SpecCrypto.get_auth_material Responder method)
  -> msg3_buff:lbuffer uint8 msg3_len
  -> ST.Stack c_response
  (requires fun h0 -> live h0 entropy_p
    /\ is_valid_hs_mem h0 hs_m /\ is_legit_hs_mem h0 hs_m
    /\
    (let hs = eval_hs_mem h0 hs_m in
      method == hs.method)
    /\ is_valid_party_state_mem h0 is_m /\ is_legit_party_state_mem h0 is_m
    /\ is_valid_plaintext2_mem h0 ptx2_m /\ live h0 msg3_buff
    /\ ( let tag_size_v = size (SpecCrypto.aead_tag_size (SpecCrypto.get_aead_alg cs)) in
      msg3_len = plaintext3_len_fixed_v cs (SpecCrypto.get_auth_material Initiator method)
        +! tag_size_v
    )
    // disjoint clauses
    /\ hs_mem_disjoint_to_ps_mem hs_m is_m /\ hs_mem_disjoint_to hs_m entropy_p
    /\ hs_mem_disjoint_to_ptx2 hs_m ptx2_m /\ hs_mem_disjoint_to hs_m msg3_buff
    /\ ps_mem_disjoint_to_ptx2 is_m ptx2_m /\ party_state_mem_disjoint_to is_m msg3_buff
    /\ party_state_mem_disjoint_to is_m entropy_p
    /\ plaintext2_mem_disjoint_to_buffer ptx2_m msg3_buff
    /\ plaintext2_mem_disjoint_to_buffer ptx2_m entropy_p
    /\ disjoint msg3_buff entropy_p
  )
  (ensures fun h0 cres h1 ->
    let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
    let is = eval_party_state_mem h0 is_m in
    let hs = eval_hs_mem h0 hs_m in
    let ptx2 = plaintext2_mem_to_plaintext2 h0 ptx2_m in

    lemma_initiator_send_msg3_respond_component_equiv #cs e0_v is hs ptx2;
    let res_abstract = Spec.initiator_send_msg3 #cs e0_v is hs ptx2 in

    (cres == CSuccess \/ cres == CInvalidECPoint \/ cres == CUnsupportedAlgorithmOrInvalidConfig)
    // /\ is_legit_hs_mem h1 hs_m
    // Lemmas for verifying the functional correctness to the abstract function
    // /\ (cres == CSuccess ==> Res? res_abstract)
    // /\ (cres == CSuccess ==> (
    //   match res_abstract with Res (msg3, hs') ->
    //     let hs'_eval = eval_hs_mem h1 hs_m in

    //     Seq.length msg3 = length msg3_buff
    //     /\ Seq.equal msg3 (as_seq h1 msg3_buff)
    //     /\ Spec.hs_equal_after_msg3 #cs hs' hs'_eval
    // ))
  )
