module Spec.EDHOC.CryptoPrimitives

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module Seq = Lib.Sequence

open FStar.Seq

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

module DH = Spec.Agile.DH
module HACLRandom = Lib.RandomSequence

module Hash = Spec.Agile.Hash
open Spec.Agile.Hash
module HashDef = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD
open Spec.Agile.AEAD
module HMAC = Spec.Agile.HMAC
open Spec.Agile.HMAC
module HKDF = Spec.Agile.HKDF
open Spec.Agile.HKDF
module P256 = Spec.P256
module Ed25519 = Spec.Ed25519

open Lib.ByteSequence
open FStar.Mul

friend Spec.Agile.HKDF


(*------------------ DH*)
// let alg_dh #a = DH.dh a


(*------------------ AEAD*)
let alg_aead_encrypt a k iv aad msg =
  AEAD.encrypt #a k iv aad msg

let lemma_alg_aead_encrypt_spec_aead_encrypt_equiv a key iv aad msg
  = ()

let alg_aead_decrypt a k iv aad ciphertext =
  AEAD.decrypt #a k iv aad ciphertext

let lemma_alg_aead_decrypt_spec_aead_decrypt_equiv a key iv aad ciphertext
  = ()

let alg_aead_correctness a k iv aad msg =
  AEAD.correctness #a k iv aad msg


(*------------------- Hash*)
let alg_do_hash a input  =
  // if (HashDef.is_shake a)
  // // Shake hash family hash variable output length
  // // so we need to specify the desired length
  // then Hash.hash' a input hash_default_size
  // else Hash.hash a input
  Hash.hash a input

let lemma_alg_do_hash_spec_hash_equiv a input
  = ()

(*------------------- HMAC*)
let alg_hmac a key data =
  HMAC.hmac a key data

let lemma_alg_hmac_spec_hmac_equiv a key data
  = ()


(*------------------- HKDF*)
let alg_hkdf_expand a prk info len =
  HKDF.expand a prk info len

let lemma_alg_hkdf_expand_spec_expand_equiv a prk info len
  = ()

let alg_hkdf_extract a salt ikm =
  HKDF.extract a salt ikm

let lemma_alg_hkdf_extract_spec_extract_equiv a salt ikm
  = ()

(*------------------- ECDSA*)
let alg_ecdsa_sign sa ha op_nonce msg priv_key =
  match sa with
    | DH_P256 -> (
      // let nonce = HACLRandom.unsound_crypto_random2 nonceP256_size in
      let msg_len:size_nat = length msg in
      P256.ecdsa_signature_agile (P256.Hash ha) msg_len msg priv_key (Some?.v op_nonce)
    )
    | DH_Curve25519 -> (
      Some (Ed25519.sign priv_key msg)
    )

let lemma_alg_ecdsa_sign_ed25519_returns_Some ha op_nonce msg priv_key
  = ()

let lemma_alg_ecdsa_sign_p256_returns_option ha op_nonce msg priv_key
  = ()

let alg_ecdsa_verify sa ha msg pub_key signature =
  match sa with
    | DH_P256 -> (
      let sig_r, sig_s = split_signature signature in
      let msg_len:size_nat = length msg in
      P256.ecdsa_verification_agile (P256.Hash ha) msg_len msg pub_key sig_r sig_s
    )
    | DH_Curve25519 -> (
      Ed25519.verify pub_key msg signature
    )

let lemma_alg_ecdsa_verify_p256_spec_equiv ha msg pub_key signature
  = ()

let lemma_alg_ecdsa_verify_ed25519_spec_equiv ha msg pub_key signature
  = ()

(*----------------------- Stream Cipher XOR*)
#push-options "--max_ifuel 8 --max_fuel 8"
let xor #len msg key =
  // lseq type
  Seq.map2 (logxor #U8 #SEC) msg key
#pop-options

let lemma_xor_map2_logxor_equiv #len b1 b2
  = ()

/// NOTE! Needs to be explicitly proved later.
let lemma_xor_involution msg key
  = admit ()

let construct_ec_keypair #cs sk
  = let pk: option (ec_pub_key cs) = secret_to_public sk in
  match pk with
  | None -> None
  | Some pk_v -> (
    let keypair:ec_keypair cs = {
      pub = pk_v;
      priv = sk
    }
    in
    Some keypair
  )

let lemma_construct_ec_keypair_equiv #cs sk
  = match secret_to_public sk with
  | None ->
    // construct_ec_keypair returns None as well
    assert (construct_ec_keypair sk == None)
  | Some pk ->
    // construct_ec_keypair returns Some {pub = pk; priv = sk}
    let temp:ec_keypair cs = { pub = pk; priv = sk } in
    let expected = Some temp in
    assert (construct_ec_keypair sk == expected)

let generate_ec_keypair cs entr =
  let (entr1, sk)
    = HACLRandom.crypto_random entr (ec_priv_key_size (get_ec_alg cs)) in
  let pk_opt = secret_to_public #cs sk in
  match pk_opt with
  | None -> None
  | Some pk_v -> (
    let keypair:ec_keypair cs = {
      pub = pk_v;
      priv = sk
    }
    in
    Some (keypair, entr1)
  )

let lemma_generate_ec_keypair_some_secret_to_public cs entr
  = let (entr1, sk)
    = HACLRandom.crypto_random entr (ec_priv_key_size (get_ec_alg cs)) in
  lemma_construct_ec_keypair_equiv sk;
  ()

let generate_ec_signature_keypair cs entr =
  let (entr1, sk)
    = HACLRandom.crypto_random entr (ec_priv_key_size (get_signature_alg cs)) in
  let pk:option (ec_signature_pub_key cs) = secret_to_public_signature_key #cs sk in
  match pk with
    | None -> None
    | Some pk_v -> (
      let signature_keypair:ec_signature_keypair cs = {
        pub = pk_v;
        priv = sk;
      }
      in
      Some (signature_keypair, entr1)
    )