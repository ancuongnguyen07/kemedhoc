module Impl.KEMEDHOC.CryptoPrimitives

open Lib.ByteBuffer
open Lib.Buffer
open Lib.ByteSequence
open Lib.IntTypes
open LowStar.BufferOps

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module Spec = Spec.KEMEDHOC.CryptoPrimitives

open Impl.KEMEDHOC.Types

module ImplEdhocCrypto = Impl.EDHOC.CryptoPrimitives
module SpecEdhocCrypto = Spec.EDHOC.CryptoPrimitives

module ImplAEAD = EverCrypt.AEAD
module SpecAEAD = Spec.Agile.AEAD

/// Frodo Impl modules
module ImplFrodo = Hacl.Frodo.KEM
module ImplFrodoRand = Hacl.Frodo.Random

module SpecHash = Spec.Agile.Hash
module DefHash = Spec.Hash.Definitions

open Lib.RandomBuffer.System
// open Lib.RandomSequence
module HACLRandom = Lib.RandomSequence

/// Re-declare here the supportedKemCipherSuite type
/// just for avoid typing the prefix `Spec`
inline_for_extraction
let supportedKemCipherSuite = Spec.supportedKemCipherSuite
inline_for_extraction
let supportedKemAlg = Spec.supportedKemAlg


(*------------------ AEAD*)
inline_for_extraction
let aead_config_pre (kcs: supportedKemCipherSuite) = ImplAEAD.config_pre (Spec.get_aead_alg kcs)

let aead_encrypt (kcs: supportedKemCipherSuite)
  : ImplEdhocCrypto.aead_encrypt_st (Spec.get_aead_alg kcs) (aead_config_pre kcs)
  = match (Spec.get_aead_alg kcs) with
    | SpecAEAD.AES128_GCM -> ImplEdhocCrypto.aead_aes128_gcm_encrypt
    | SpecAEAD.AES256_GCM -> ImplEdhocCrypto.aead_aes256_gcm_encrypt

let aead_decrypt (kcs: supportedKemCipherSuite)
  : ImplEdhocCrypto.aead_decrypt_st (Spec.get_aead_alg kcs) (aead_config_pre kcs)
  = match (Spec.get_aead_alg kcs) with
    | SpecAEAD.AES128_GCM -> ImplEdhocCrypto.aead_aes128_gcm_decrypt
    | SpecAEAD.AES256_GCM -> ImplEdhocCrypto.aead_aes256_gcm_decrypt

(*------------------ Hash*)
inline_for_extraction
let hash_pre (kcs: supportedKemCipherSuite)
  : Type0
  = match (Spec.get_hash_alg kcs) with
    | SpecHash.SHA2_256 -> True

let do_hash (kcs: supportedKemCipherSuite)
  : ImplEdhocCrypto.do_hash_st (Spec.get_hash_alg kcs) (hash_pre kcs)
  = match (Spec.get_hash_alg kcs) with
    | SpecHash.SHA2_256 -> ImplEdhocCrypto.hash_sha2_256

(*------------------ HKDF*)
let hkdf_expand (kcs: supportedKemCipherSuite)
  : ImplEdhocCrypto.hkdf_expand_st (Spec.get_hash_alg kcs)
  = match (Spec.get_hash_alg kcs) with
    | SpecHash.SHA2_256 -> ImplEdhocCrypto.hkdf_expand_sha2_256

let hkdf_extract (kcs: supportedKemCipherSuite)
  : ImplEdhocCrypto.hkdf_extract_st (Spec.get_hash_alg kcs)
  = match (Spec.get_hash_alg kcs) with
    | SpecHash.SHA2_256 -> ImplEdhocCrypto.hkdf_extract_sha2_256

(*------------------ KEM*)
// let kem_state = B.gcmalloc HyperStack.root 0ul 48ul
let kem_state = ImplFrodoRand.state

/// KEM key generation
inline_for_extraction noextract
type kem_keygen_st (a: supportedKemAlg)
  = pk: alg_kem_pub_key_buff a
  -> sk: alg_kem_priv_key_buff a
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 entropy_p /\ live h0 pk /\ live h0 sk
    /\ B.all_disjoint [loc pk; loc sk; loc entropy_p; loc kem_state]
  )
  (ensures fun h0 _ h1 ->
    modifies (loc kem_state |+| loc pk |+| loc sk |+| loc entropy_p) h0 h1
    /\ (
      let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
      let (pk_s, sk_s) = Spec.alg_kem_keygen a e0_v in

      Seq.equal (as_seq h1 pk) pk_s
      /\ Seq.equal (as_seq h1 sk) sk_s
    )
  )

inline_for_extraction
val kem_keygen_frodo640: kem_keygen_st Spec.Frodo640

let kem_keygen (kcs: supportedKemCipherSuite)
  = match (Spec.get_kem_alg kcs) with
    | Spec.Frodo640 -> kem_keygen_frodo640

/// KEM encapsulation
inline_for_extraction noextract
type kem_encaps_st (a: supportedKemAlg)
  = pk: alg_kem_pub_key_buff a
  -> ct: alg_kem_ciphertext_buff a
  -> ss: alg_kem_shared_secret_buff a
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 entropy_p /\ live h0 pk /\ live h0 ct /\ live h0 ss
    /\ B.all_disjoint [loc pk; loc entropy_p; loc kem_state; loc ct; loc ss]
  )
  (ensures fun h0 _ h1 ->
    modifies (loc entropy_p |+| loc kem_state |+| loc ct |+| loc ss) h0 h1
    /\ (
      let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
      let pk_s = as_seq h0 pk in
      let (ct_s, ss_s) = Spec.alg_kem_encaps a e0_v pk_s in

      Seq.equal (as_seq h1 ct) ct_s
      /\ Seq.equal (as_seq h1 ss) ss_s
    )
  )

inline_for_extraction
val kem_encaps_frodo640: kem_encaps_st Spec.Frodo640

let kem_encaps (kcs: supportedKemCipherSuite)
  = match (Spec.get_kem_alg kcs) with
    | Spec.Frodo640 -> kem_encaps_frodo640

/// KEM decapsulation
inline_for_extraction noextract
type kem_decaps_st (a: supportedKemAlg)
  = sk: alg_kem_priv_key_buff a
  -> ct: alg_kem_ciphertext_buff a
  -> ss: alg_kem_shared_secret_buff a
  -> ST.Stack unit
  (requires fun h0 -> 
    live h0 sk /\ live h0 ct /\ live h0 ss
    /\ B.all_disjoint [loc sk; loc ct; loc ss]
  )
  (ensures fun h0 _ h1 ->
    modifies1 ss h0 h1
    /\ (
      let ss_s = Spec.alg_kem_decaps a (as_seq h0 ct) (as_seq h0 sk) in
      Seq.equal (as_seq h1 ss) ss_s
    )
  )

inline_for_extraction
val kem_decaps_frodo640: kem_decaps_st Spec.Frodo640

let kem_decaps (kcs: supportedKemCipherSuite)
  = match (Spec.get_kem_alg kcs) with
    | Spec.Frodo640 -> kem_decaps_frodo640