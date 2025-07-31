module Impl.EDHOC.Core.Msg3.Aux

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

open Impl.EDHOC.CryptoPrimitives
open Impl.EDHOC.Parser
open Impl.EDHOC.KeySchedule
// open Impl.EDHOC.TranscriptHash
open Impl.EDHOC.Core.Types
open Impl.EDHOC.Utilities
open TypeHelper.EDHOC


module HACLRandom = Lib.RandomSequence

(*--------------------------- Common Things*)
/// Disjoint clauses

/// Clauses for Plaintext3 mem
let hs_mem_disjoint_to_ptx3 (#cs:SpecCrypto.supported_cipherSuite)
  (#auth_material:SpecCrypto.authentication_material)
  (hs_m:hs_mem #cs) (ptx3_m:plaintext3_mem #cs #auth_material)
  = match ptx3_m with id_cred_i, sig_or_mac3, ead3 -> (
    hs_mem_disjoint_to hs_m id_cred_i /\ hs_mem_disjoint_to hs_m sig_or_mac3
    /\ hs_mem_disjoint_to hs_m ead3
  )

let ps_mem_disjoint_to_ptx3 (#cs:SpecCrypto.supported_cipherSuite)
  (#auth_material:SpecCrypto.authentication_material)
  (ps_m:party_state_mem #cs) (ptx3_m:plaintext3_mem #cs #auth_material)
  = match ptx3_m with id_cred_i, sig_or_mac3, ead3 -> (
    party_state_mem_disjoint_to ps_m id_cred_i /\ party_state_mem_disjoint_to ps_m sig_or_mac3
    /\ party_state_mem_disjoint_to ps_m ead3
  )

/// Message3 is not a tuple, it is just a single lbuffer
/// so there is no need to do unfolding disjoint clauses

(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)
/// verify Sig_or_MAC3
val verify_sig_or_mac3:
  #cs:SpecCrypto.supported_cipherSuite
  -> auth_material:SpecCrypto.authentication_material
  -> sig_or_mac3_m:lbuffer uint8 (sig_or_mac23_size_v cs auth_material)
  -> mac3_m:lbuffer uint8 (mac23_size_v cs auth_material)
  -> context3_m:context3_mem #cs
  -> pk_i_m:opt_ecdsa_pub_key_buf cs
  -> ST.Stack bool
  (requires fun h0 ->
    live h0 sig_or_mac3_m /\ live h0 mac3_m /\ live h0 pk_i_m
    /\ is_valid_context3_mem h0 context3_m
    /\ B.all_disjoint [loc sig_or_mac3_m; loc mac3_m; loc pk_i_m]
    /\ context3_mem_disjoint_to context3_m sig_or_mac3_m
    /\ context3_mem_disjoint_to context3_m mac3_m
    /\ context3_mem_disjoint_to context3_m pk_i_m
    /\ (auth_material == SpecCrypto.Signature ==> ~(g_is_null pk_i_m))
  )
  (ensures fun h0 res h1 ->
    let sig_or_mac3 = as_seq h0 sig_or_mac3_m in
    let mac3 = as_seq h0 mac3_m in
    let c3 = context3_mem_to_context3 h0 context3_m in
    let pk_i = lbuffer_or_null_as_seq h0 pk_i_m in

    let res_abstract = Spec.verify_sig_or_mac3 #cs auth_material sig_or_mac3 mac3 c3 pk_i in

    modifies0 h0 h1
    /\ (res <==> res_abstract)
  )

(*-------------------------------------------*)
(*---------------------------- Initiator side*)
(*-------------------------------------------*)
/// derive Sig_or_MAC3
val derive_sig_or_mac3:
  #cs:SpecCrypto.supported_cipherSuite
  -> auth_material:SpecCrypto.authentication_material
  -> sk_i_m:opt_ecdsa_priv_key_buf cs
  -> mac3_m:mac23_buff cs auth_material
  -> context3_m:context3_mem #cs
  -> sig_or_mac3_m:lbuffer uint8 (sig_or_mac23_size_v cs auth_material)
  -> ST.Stack c_response
  (requires fun h0 ->
    live h0 sig_or_mac3_m /\ live h0 sk_i_m /\ live h0 mac3_m /\ live h0 entropy_p
    /\ is_valid_context3_mem h0 context3_m
    /\ B.all_disjoint [loc sk_i_m; loc mac3_m; loc sig_or_mac3_m; loc entropy_p]
    /\ context3_mem_disjoint_to context3_m sk_i_m
    /\ context3_mem_disjoint_to context3_m entropy_p
    /\ context3_mem_disjoint_to context3_m sig_or_mac3_m
    /\ context3_mem_disjoint_to context3_m mac3_m
    /\ (auth_material == SpecCrypto.Signature ==> ~(g_is_null sk_i_m))
  )
  (ensures fun h0 cres h1 -> 
    (match auth_material with
        | SpecCrypto.Signature -> modifies2 sig_or_mac3_m entropy_p h0 h1
        | SpecCrypto.MAC -> modifies1 sig_or_mac3_m h0 h1
    ) /\
    (
      let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
      let sk_i = lbuffer_or_null_as_seq h0 sk_i_m in
      let c3_abstract = context3_mem_to_context3 h0 context3_m in
      let mac3 = as_seq h0 mac3_m in

      let res_abstract = Spec.derive_sig_or_mac3 #cs auth_material e0_v sk_i mac3 c3_abstract in

      (cres == CSuccess \/ cres == CInvalidECPoint)
      /\ (Some? res_abstract <==> cres == CSuccess)
      /\ (None? res_abstract <==> cres <> CSuccess)
      /\ (cres == CSuccess ==> (
        Seq.equal (Some?.v res_abstract) (as_seq h1 sig_or_mac3_m)
      ))
    )
  )

/// Intermediate: derive PRK4e3m for Initiator
val derive_prk4e3m:
  #cs:SpecCrypto.supported_cipherSuite
  -> i_auth:SpecCrypto.authentication_material
  -> prk3e2m_m:hash_out_buff cs
  -> th3_m:hash_out_buff cs
  -> i_m:opt_ec_priv_key_buf cs
  -> pub_m:opt_ec_pub_key_buf cs
  -> prk4e3m_m:hash_out_buff cs
  -> ST.Stack c_response
  (requires fun h0 ->
    live h0 i_m /\ live h0 pub_m /\ live h0 prk4e3m_m
    /\ live h0 prk3e2m_m /\ live h0 th3_m
    /\ B.all_disjoint [loc i_m; loc pub_m; loc prk3e2m_m; loc th3_m; loc prk4e3m_m]
    /\ (i_auth == SpecCrypto.MAC ==> (~(g_is_null i_m) /\ ~(g_is_null pub_m)))
  )
  (ensures fun h0 cres h1 ->
    let th3 = as_seq h0 th3_m in
    let prk3e2m = as_seq h0 prk3e2m_m in
    let i = lbuffer_or_null_as_seq h0 i_m in
    let pub = lbuffer_or_null_as_seq h0 pub_m in

    let res_abstract = Spec.derive_prk4e3m #cs i_auth prk3e2m th3 i pub in

    (cres == CSuccess \/ cres == CInvalidECPoint)
    /\ (Res? res_abstract <==> cres == CSuccess)
    /\ (Fail? res_abstract <==> cres <> CSuccess)
    /\ (cres == CSuccess ==> (
      let prk4e3m_spec = match res_abstract with Res k -> k in

      modifies1 prk4e3m_m h0 h1
      /\ Seq.equal prk4e3m_spec (as_seq h1 prk4e3m_m)
    ))
    /\ (cres <> CSuccess ==> modifies0 h0 h1)
  )
