module Impl.EDHOC.Core.Msg2.Aux

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
module SpecEnc = Spec.EDHOC.Ciphertext

open Spec.EDHOC.Base.Definitions
// open Spec.EDHOC.Serialization

open Impl.EDHOC.CryptoPrimitives
open Impl.EDHOC.KeySchedule
open Impl.EDHOC.Ciphertext
open Impl.EDHOC.TranscriptHash
open Impl.EDHOC.Parser
open Impl.EDHOC.Utilities
open Impl.EDHOC.Core.Types
open TypeHelper.EDHOC

module HACLRandom = Lib.RandomSequence

(*--------------------------- Common Things*)
/// Disjoint clauses

/// Clauses for Message2 mem
let hs_mem_disjoint_to_msg2 (#cs:SpecCrypto.supported_cipherSuite)
  (#auth_material:SpecCrypto.authentication_material)
  (hs_m:hs_mem #cs) (msg2_m:message2_mem #cs #auth_material)
  = match msg2_m with pub_m, c2_m -> (
      hs_mem_disjoint_to hs_m pub_m /\ hs_mem_disjoint_to hs_m c2_m
    )

let ps_mem_disjoint_to_msg2 (#cs:SpecCrypto.supported_cipherSuite)
  (#auth_material:SpecCrypto.authentication_material)
  (ps_m:party_state_mem #cs) (msg2_m:message2_mem #cs #auth_material)
  = match msg2_m with pub_m, c2_m -> (
      party_state_mem_disjoint_to ps_m pub_m /\ party_state_mem_disjoint_to ps_m c2_m
    )

/// Clauses for Plaintext2 mem
let hs_mem_disjoint_to_ptx2 (#cs:SpecCrypto.supported_cipherSuite)
  (#auth_material:SpecCrypto.authentication_material)
  (hs_m:hs_mem #cs) (ptx2_m:plaintext2_mem #cs #auth_material)
  = match ptx2_m with c_r, id_cred_r, sig_or_mac2, ead2 -> (
      hs_mem_disjoint_to hs_m c_r /\ hs_mem_disjoint_to hs_m id_cred_r
      /\ hs_mem_disjoint_to hs_m sig_or_mac2 /\ hs_mem_disjoint_to hs_m ead2
    )

let ps_mem_disjoint_to_ptx2 (#cs:SpecCrypto.supported_cipherSuite)
  (#auth_material:SpecCrypto.authentication_material)
  (ps_m:party_state_mem #cs) (ptx2_m:plaintext2_mem #cs #auth_material)
  = match ptx2_m with c_r, id_cred_r, sig_or_mac2, ead2 -> (
      party_state_mem_disjoint_to ps_m c_r /\ party_state_mem_disjoint_to ps_m id_cred_r
      /\ party_state_mem_disjoint_to ps_m sig_or_mac2 /\ party_state_mem_disjoint_to ps_m ead2
    ) 


/// Disjoint clauses between Plaintext2 and Message2 mem
let message2_mem_disjoint_to_ptx2 (#cs:SpecCrypto.supported_cipherSuite)
  (#auth_material:SpecCrypto.authentication_material)
  (msg2_m:message2_mem #cs #auth_material)
  (ptx2_m:plaintext2_mem #cs #auth_material)
  = match ptx2_m with c_r, id_cred_r, sig_or_mac2, ead2 -> (
      message2_mem_disjoint_to msg2_m c_r /\ message2_mem_disjoint_to msg2_m id_cred_r
      /\ message2_mem_disjoint_to msg2_m sig_or_mac2 /\ message2_mem_disjoint_to msg2_m ead2
    ) 

(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)

/// verify Sig_or_Mac2
val verify_sig_or_mac2:
  #cs:SpecCrypto.supported_cipherSuite
  -> auth_material:SpecCrypto.authentication_material
  -> sig_or_mac2_m:lbuffer uint8 (sig_or_mac23_size_v cs auth_material)
  -> mac2_m:lbuffer uint8 (mac23_size_v cs auth_material)
  -> context2_m:context2_mem #cs
  -> pk_r_m:opt_ecdsa_pub_key_buf cs
  -> ST.Stack bool
  (requires fun h0 ->
    live h0 sig_or_mac2_m /\ live h0 mac2_m /\ live h0 pk_r_m
    /\ is_valid_context2_mem h0 context2_m
    /\ B.all_disjoint [loc sig_or_mac2_m; loc mac2_m; loc pk_r_m]
    /\ context2_mem_disjoint_to context2_m sig_or_mac2_m
    /\ context2_mem_disjoint_to context2_m mac2_m
    /\ context2_mem_disjoint_to context2_m pk_r_m
    /\ (auth_material == SpecCrypto.Signature ==> ~(g_is_null pk_r_m))
  )
  (ensures fun h0 res h1 ->
    let sig_or_mac2 = as_seq h0 sig_or_mac2_m in
    let mac2 = as_seq h0 mac2_m in
    let c2 = context2_mem_to_context2 h0 context2_m in
    let pk_r = lbuffer_or_null_as_seq h0 pk_r_m in

    let res_abstract = Spec.verify_sig_or_mac2 #cs auth_material sig_or_mac2 mac2 c2 pk_r in
    
    modifies0 h0 h1 /\
    (res <==> res_abstract)
  )

/// derive Sig_or_Mac2
val derive_sig_or_mac2:
  #cs:SpecCrypto.supported_cipherSuite
  -> auth_material:SpecCrypto.authentication_material
  -> sk_r_m:opt_ecdsa_priv_key_buf cs
  // -> mac2_len:size_t{mac2_len = mac23_size_v cs auth_material}
  -> mac2_m:mac23_buff cs auth_material
  -> context2_m:context2_mem #cs
  -> sig_or_mac2_m:lbuffer uint8 (sig_or_mac23_size_v cs auth_material)
  -> ST.Stack c_response
  (requires fun h0 ->
    live h0 sig_or_mac2_m /\ live h0 mac2_m /\ live h0 sk_r_m /\ live h0 entropy_p
    /\ is_valid_context2_mem h0 context2_m
    /\ B.all_disjoint [loc sk_r_m; loc mac2_m; loc sig_or_mac2_m; loc entropy_p]
    /\ context2_mem_disjoint_to context2_m sk_r_m
    /\ context2_mem_disjoint_to context2_m entropy_p
    /\ context2_mem_disjoint_to context2_m sig_or_mac2_m
    /\ context2_mem_disjoint_to context2_m mac2_m
    /\ (auth_material == SpecCrypto.Signature ==> ~(g_is_null sk_r_m))
  )
  (ensures fun h0 res h1 ->
    
    (match auth_material with
        | SpecCrypto.Signature -> modifies2 sig_or_mac2_m entropy_p h0 h1
        | SpecCrypto.MAC -> modifies1 sig_or_mac2_m h0 h1
    )
    /\ (
      let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
      let sk_r = lbuffer_or_null_as_seq h0 sk_r_m in
      let c2_abstract = context2_mem_to_context2 h0 context2_m in
      let mac2 = as_seq h0 mac2_m in

      let res_abstract = Spec.derive_sig_or_mac2 #cs auth_material e0_v sk_r mac2 c2_abstract in

      (res == CSuccess \/ res == CInvalidECPoint)
      /\ (Some? res_abstract <==> res == CSuccess)
      /\ (res == CSuccess ==> (
        Seq.equal (Some?.v res_abstract) (as_seq h1 sig_or_mac2_m)
      ))
    )
  )


/// Intermediate: derive PRK3e2m for Responder
val derive_prk3e2m:
  #cs:SpecCrypto.supported_cipherSuite
  -> r_auth:SpecCrypto.authentication_material
  -> prk2e_m:hash_out_buff cs
  -> th2_m:hash_out_buff cs
  -> r_m:opt_ec_priv_key_buf cs
  -> pub_m:opt_ec_pub_key_buf cs
  // -> hs_m:hs_mem #cs
  -> prk3e2m_m:hash_out_buff cs
  -> ST.Stack c_response
  (requires fun h0 ->
    // is_valid_hs_mem h0 hs_m /\ is_legit_hs_mem h0 hs_m
    // /\ live h0 r_m /\ hs_mem_disjoint_to hs_m r_m
    live h0 r_m /\ live h0 pub_m /\ live h0 prk3e2m_m
    /\ live h0 prk2e_m /\ live h0 th2_m
    /\ B.all_disjoint [loc r_m; loc pub_m; loc prk2e_m; loc th2_m; loc prk3e2m_m]
    /\ (r_auth == SpecCrypto.MAC ==> (~(g_is_null r_m) /\ ~(g_is_null pub_m)))
  )
  (ensures fun h0 cres h1 -> (
    let th2 = as_seq h0 th2_m in
    let prk2e = as_seq h0 prk2e_m in
    // let hs_abstract = eval_hs_mem h0 hs_m in
    let r = lbuffer_or_null_as_seq h0 r_m in
    let pub = lbuffer_or_null_as_seq h0 pub_m in

    let res_abstract = Spec.derive_prk3e2m #cs r_auth prk2e th2 r pub in

    /// Requirements
    (cres == CSuccess \/ cres == CInvalidECPoint)
    /\ (Res? res_abstract <==> cres == CSuccess)
    /\ (cres == CSuccess ==> ( 
        let prk3e2m_spec = match res_abstract with Res k -> k in

        modifies1 prk3e2m_m h0 h1
        /\ Seq.equal (prk3e2m_spec) (as_seq h1 prk3e2m_m)
    ))
    /\ (cres <> CSuccess ==> modifies0 h0 h1)
  ))
