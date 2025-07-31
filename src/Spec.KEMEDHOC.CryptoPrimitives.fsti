module Spec.KEMEDHOC.CryptoPrimitives

(*Pre-quantum crypto modules*)
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Hash.Definitions

(*HACL modules*)
open Lib.Buffer
// open Lib.Sequence
open Lib.RawIntTypes
open Lib.IntTypes
open Lib.ByteSequence
open Lib.RandomSequence
module Seq = Lib.Sequence

(*EDHOC modules*)
open Spec.EDHOC.CryptoPrimitives


/// KEM algorithms
type kemAlg =
  | ML_KEM_512 | ML_KEM_768 | ML_KEM_1024
let is_supported_kemAlg (a:kemAlg) : bool
  = match a with | ML_KEM_512 -> true
                 | _ -> false
type supported_kemAlg = a:kemAlg{is_supported_kemAlg a}

/// KEM-supported ciphersuites
type kem_cipherSuite = aeadAlg & hashAlg & supported_kemAlg
let is_supported_kem_cipherSuite (cs:kem_cipherSuite) : bool
  = match cs with
    | AEAD.AES128_GCM, Hash.SHA2_256, ML_KEM_512 -> true
    | _ -> false
type supported_kem_cipherSuite
  = cs:kem_cipherSuite{is_supported_kem_cipherSuite cs}

/// KEM-supported ciphersuite label
let kem_cipherSuite_label (kcs:supported_kem_cipherSuite) : nat
  = match kcs with
    | AEAD.AES128_GCM, Hash.SHA2_256, ML_KEM_512 -> 8

// Getters for `kem_cipherSuite`
let kcs_get_aead_alg (kcs:kem_cipherSuite)
  = match kcs with aead_alg, _, _ -> aead_alg
let kcs_get_hash_alg (kcs:kem_cipherSuite)
  = match kcs with _, hash_alg, _ -> hash_alg
let kcs_get_kem_alg (kcs:kem_cipherSuite)
  = match kcs with _, _, kem_alg -> kem_alg


(*----------------- ML-KEM constants*)
/// Applied to ll variant of ML-KEM
let ml_kem_shared_secret_size = 32
let ml_kem_keypair_seed_size = 64

(*----------------- ML-KEM 512 Constants*)
let ml_kem_pub_key_size (kcs:supported_kem_cipherSuite)
  : size_nat
  = match (kcs_get_kem_alg kcs) with
    | ML_KEM_512 -> 800
let ml_kem_priv_key_size (kcs:supported_kem_cipherSuite)
  : size_nat
  = match (kcs_get_kem_alg kcs) with
    | ML_KEM_512 -> 1632
let ml_kem_ciphertext_size (kcs:supported_kem_cipherSuite)
  : size_nat
  = match (kcs_get_kem_alg kcs) with
    | ML_KEM_512 -> 768

(*----------------- ML-KEM keys and ciphertext*)
let ml_kem_pub_key (kcs:supported_kem_cipherSuite)
  = lbytes (ml_kem_pub_key_size kcs)
let ml_kem_priv_key (kcs:supported_kem_cipherSuite)
  = lbytes (ml_kem_priv_key_size kcs)
let ml_kem_ciphertext (kcs:supported_kem_cipherSuite)
  = lbytes (ml_kem_ciphertext_size kcs)

let ml_kem_shared_secret = lbytes ml_kem_shared_secret_size

(*---------------- ML-KEM keypair*)
noeq type ml_kem_keypair (#kcs:supported_kem_cipherSuite) = {
  pub:ml_kem_pub_key kcs;
  priv:ml_kem_priv_key kcs;
}

/// the bundle of KEM ciphertext and shared secret
noeq type ml_kem_cipher_ss (#kcs:supported_kem_cipherSuite) = {
  ciphertext:ml_kem_ciphertext kcs;
  ss:ml_kem_shared_secret;
}

/// This implementation only considers ML-KEM-512
/// but still provides a generic API for scalability
/// The APIs apply to all secure KEM schemes

/// Key Generation
val ml_kem_key_generation:
  kcs:supported_kem_cipherSuite
  -> entr:entropy
  -> option (ml_kem_keypair #kcs)

/// KEM Encapsulation
val ml_kem_encapsulation:
  kcs:supported_kem_cipherSuite
  -> pub:ml_kem_pub_key kcs
  -> entr:entropy
  -> option (ml_kem_cipher_ss #kcs)

/// KEM Decapsulation
val ml_kem_decapsulation:
  kcs:supported_kem_cipherSuite
  -> priv:ml_kem_priv_key kcs
  -> ciphertext:ml_kem_ciphertext kcs
  -> option (ml_kem_shared_secret)

/// Lemmas
let ml_kem_encap_decap_equiv
  (kcs:supported_kem_cipherSuite) (kp:ml_kem_keypair #kcs)
  (entr:entropy)
  : Lemma (ensures (
    let res_encap = ml_kem_encapsulation kcs kp.pub entr in
    if (not(Some? res_encap)) then True
    else (
      let cipher_ss = Some?.v res_encap in
      let res_decap = ml_kem_decapsulation kcs kp.priv cipher_ss.ciphertext in

      if (not(Some? res_decap)) then True
      else (
        let decaped_ss = Some?.v res_decap in

        Seq.equal decaped_ss cipher_ss.ss
      )
    )
  ))
  = admit()
