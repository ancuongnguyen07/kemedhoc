module Impl.EDHOC.Core.Msg2

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

open Impl.EDHOC.CryptoPrimitives
open Impl.EDHOC.KeySchedule
open Impl.EDHOC.Ciphertext
open Impl.EDHOC.TranscriptHash
open Impl.EDHOC.Parser
open Impl.EDHOC.Utilities
open Impl.EDHOC.Core.Types
open TypeHelper.EDHOC

open Impl.EDHOC.Core.Msg2.Aux

module HACLRandom = Lib.RandomSequence

(*-------------------------------------------*)
(*---------------------------- Initiator side*)
(*-------------------------------------------*)
val initiator_process_msg2:
  #cs:SpecCrypto.supported_cipherSuite
  -> local_auth_material:SpecCrypto.authentication_material
  -> remote_auth_material:SpecCrypto.authentication_material
  -> is_m:party_state_mem_shared_est #cs
  -> hs_m:hs_mem #cs
  -> msg2_m:message2_mem #cs #remote_auth_material
  -> ST.Stack c_response
  (requires fun h0 -> live h0 entropy_p /\
    is_valid_party_state_mem h0 is_m /\ is_valid_hs_mem h0 hs_m
    /\ is_legit_hs_mem h0 hs_m /\ is_valid_message2_mem h0 msg2_m
    /\ hs_mem_disjoint_to_ps_mem hs_m is_m
    /\ hs_mem_disjoint_to_msg2 hs_m msg2_m
    /\ ps_mem_disjoint_to_msg2 is_m msg2_m
    // disjoint clauses to entropy_p
    /\ hs_mem_disjoint_to hs_m entropy_p /\ party_state_mem_disjoint_to is_m entropy_p
    /\ message2_mem_disjoint_to msg2_m entropy_p
    /\ (
      let hs = eval_hs_mem h0 hs_m in
      local_auth_material == (SpecCrypto.get_auth_material Initiator hs.method)
      /\ remote_auth_material == (SpecCrypto.get_auth_material Responder hs.method)
    )
  )
  (ensures fun h0 cres h1 ->
    (cres == CSuccess \/ cres == CInvalidECPoint \/ cres == CIntegrityCheckFailed
    \/ cres == CInvalidCredential \/ cres == CUnknownCredentialID)
  )

(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)
val responder_send_msg2:
  #cs:SpecCrypto.supported_cipherSuite
  -> #auth_material:SpecCrypto.authentication_material
  -> #ptx2_len:size_t{ptx2_len = plaintext2_len_fixed_v cs auth_material}
  -> #msg2_len:size_t{msg2_len = size (size_v ptx2_len + SpecCrypto.ec_pub_key_size (SpecCrypto.get_ec_alg cs))}
  -> ptx2_buff:lbuffer uint8 ptx2_len
  -> msg2_buff:lbuffer uint8 msg2_len
  -> rs_m:party_state_mem_shared_est #cs
  -> hs_m:hs_mem #cs
  -> ST.Stack c_response
  (requires fun h0 -> live h0 entropy_p /\
    // is_valid_message2_mem h0 msg2_buff /\ is_valid_plaintext2_mem h0 ptx2_buff
    live h0 msg2_buff /\ live h0 ptx2_buff
    /\ is_valid_party_state_mem h0 rs_m /\ is_valid_hs_mem h0 hs_m
    /\ is_legit_party_state_mem h0 rs_m /\ is_legit_hs_mem h0 hs_m
    /\ ecdsa_sig_keypair_mem_live h0 (ps_mem_get_sig_kp rs_m)
    // disjoint clauses
    /\ (
      hs_mem_disjoint_to_ps_mem hs_m rs_m
      // /\ hs_mem_disjoint_to_msg2 hs_m msg2_buff /\ hs_mem_disjoint_to_ptx2 hs_m ptx2_buff
      /\ hs_mem_disjoint_to hs_m msg2_buff /\ hs_mem_disjoint_to hs_m ptx2_buff 
      /\ party_state_mem_disjoint_to rs_m msg2_buff /\ party_state_mem_disjoint_to rs_m ptx2_buff
      // /\ message2_mem_disjoint_to_ptx2 msg2_buff ptx2_buff
      /\ B.all_disjoint [loc msg2_buff; loc ptx2_buff; loc entropy_p]
      // disjoint to entropy_p clauses
      /\ hs_mem_disjoint_to hs_m entropy_p /\ party_state_mem_disjoint_to rs_m entropy_p
      // /\ message2_mem_disjoint_to msg2_buff entropy_p /\ plaintext2_mem_disjoint_to_buffer ptx2_buff entropy_p
    )
    /\ auth_material == SpecCrypto.get_auth_material Responder (eval_hs_mem h0 hs_m).method
    /\ (auth_material == SpecCrypto.MAC ==> ~(g_is_null hs_m.g_rx))
  )
  (ensures fun h0 cres h1 -> (
    // modifies clauses
    (cres == CSuccess \/ cres == CInvalidECPoint)
    
  ))
