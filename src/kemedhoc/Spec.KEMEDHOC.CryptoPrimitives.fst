module Spec.KEMEDHOC.CryptoPrimitives

module EdhocCrypto = Spec.EDHOC.CryptoPrimitives

module FrodoSpec = Spec.Frodo.KEM
module FrodoRandomSpec = Spec.Frodo.Random
module FrodoParamsSpec = Spec.Frodo.Params
module FrodoKemKeyGen = Spec.Frodo.KEM.KeyGen
module FrodoKemEncaps = Spec.Frodo.KEM.Encaps
module FrodoKemDecaps = Spec.Frodo.KEM.Decaps

module AEADSpec = Spec.Agile.AEAD
module HashSpec = Spec.Agile.Hash
module HKDFSpec = Spec.Agile.HKDF

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RandomSequence

open FStar.Mul

type kemAlg =
  | Frodo640
  | ML_KEM512

/// Currently, HACL* only has a verified implememtation of SHAKE128-based generation algorithm
inline_for_extraction
let genFrodoAlg = FrodoParamsSpec.SHAKE128

let is_supported_kem (a:kemAlg)
  : Tot bool
  = match a with
    | Frodo640 -> true
    | ML_KEM512 -> false

inline_for_extraction
let is_frodo_alg (a: kemAlg)
  : Tot bool
  = match a with
    | Frodo640 -> true
    | ML_KEM512 -> false

inline_for_extraction
type supportedKemAlg = a:kemAlg{is_supported_kem a}
inline_for_extraction
type frodoKemAlg = a:kemAlg{is_frodo_alg a}

let kemAlg_to_frodo_alg (a: frodoKemAlg)
  : Tot FrodoParamsSpec.frodo_alg
  = match a with
    | Frodo640 -> FrodoParamsSpec.Frodo640

(*
Currently, LAKE working group has not defined any CIPHERSUITE containing
KEM algorithms, we define here available lables for future use.
*)
inline_for_extraction
type kemCipherSuite = kemAlg & EdhocCrypto.aeadAlg & EdhocCrypto.hashAlg
inline_for_extraction
let get_kem_alg (kcs: kemCipherSuite)
  = match kcs with
    | kem_alg, _, _ -> kem_alg
inline_for_extraction
let get_aead_alg (kcs: kemCipherSuite)
  = match kcs with
    | _, aead_alg, _ -> aead_alg
inline_for_extraction
let get_hash_alg (kcs: kemCipherSuite)
  = match kcs with
    | _, _, hash_alg -> hash_alg

let get_kemCipherSuite_label (kcs: kemCipherSuite)
  : option nat
  = match kcs with
    | Frodo640, AEADSpec.AES128_GCM, HashSpec.SHA2_256 -> Some 9
    | _ -> None

let is_supported_kcs (kcs: kemCipherSuite)
  : bool
  = get_kemCipherSuite_label kcs <> None

inline_for_extraction
type supportedKemCipherSuite = a:kemCipherSuite{is_supported_kcs a}
inline_for_extraction
type supportedKemCipherSuiteLabel = n:nat{n = 9}

let get_kemCipherSuite_from_label (label: supportedKemCipherSuiteLabel)
  : supportedKemCipherSuite
  = match label with
    | 9 -> (Frodo640, AEADSpec.AES128_GCM, HashSpec.SHA2_256)

(* Algorithm driven:
Sizes for KEM public/private, ciphertext, and shared secret
*)
inline_for_extraction
let alg_kem_public_key_size (a: kemAlg)
  = match a with
    | Frodo640 -> FrodoParamsSpec.crypto_publickeybytes (kemAlg_to_frodo_alg a) // 9616
    | ML_KEM512 -> 800
inline_for_extraction
let alg_kem_priv_key_size (a: kemAlg)
  = match a with
    | Frodo640 -> FrodoParamsSpec.crypto_secretkeybytes (kemAlg_to_frodo_alg a) // 19888
    | ML_KEM512 -> 1632
inline_for_extraction
let alg_kem_ciphertext_size (a: kemAlg)
  = match a with
    | Frodo640 -> FrodoParamsSpec.crypto_ciphertextbytes (kemAlg_to_frodo_alg a) // 9720
    | ML_KEM512 -> 768
inline_for_extraction
let alg_kem_shared_secret_size (a: kemAlg)
  = match a with
    | Frodo640 -> FrodoParamsSpec.crypto_bytes (kemAlg_to_frodo_alg a)  // 16
    | ML_KEM512 -> 32

(* CipherSuite driven:
Sizes for KEM public/private, ciphertext, and shared secret
*)
inline_for_extraction
let kem_public_key_size (kcs: kemCipherSuite)
  = alg_kem_public_key_size (get_kem_alg kcs)
inline_for_extraction
let kem_priv_key_size (kcs: kemCipherSuite)
  = alg_kem_priv_key_size (get_kem_alg kcs)
inline_for_extraction
let kem_ciphertext_size (kcs: kemCipherSuite)
  = alg_kem_ciphertext_size (get_kem_alg kcs)
inline_for_extraction
let kem_shared_secret_size (kcs: kemCipherSuite)
  = alg_kem_shared_secret_size (get_kem_alg kcs)

(*------------------ AEAD*)

/// size for AEAD tag
inline_for_extraction
let aead_tag_size (kcs: kemCipherSuite)
  = EdhocCrypto.aead_tag_size (get_aead_alg kcs)

inline_for_extraction
let aead_iv_size = EdhocCrypto.aead_iv_size
inline_for_extraction
type aead_iv = EdhocCrypto.aead_iv
inline_for_extraction
let aead_key_size (kcs: kemCipherSuite)
  = EdhocCrypto.aead_key_size (get_aead_alg kcs)
inline_for_extraction
type aead_key (kcs: kemCipherSuite) = lbytes (aead_key_size kcs)
inline_for_extraction
type aead_valid_input (kcs: kemCipherSuite) =
  b:bytes{Seq.length b <= EdhocCrypto.alg_aead_max_input_size (get_aead_alg kcs)}
inline_for_extraction
type aead_valid_ciphertext (kcs: kemCipherSuite) =
  c:bytes{Seq.length c >= aead_tag_size kcs
          /\ Seq.length c <= EdhocCrypto.alg_aead_max_input_size (get_aead_alg kcs) + aead_tag_size kcs}

/// AEAD encryption
val aead_encrypt:
  kcs: supportedKemCipherSuite
  -> key: aead_key kcs
  -> iv: aead_iv
  -> aad: aead_valid_input kcs
  -> msg: aead_valid_input kcs
  -> lbytes (Seq.length msg + aead_tag_size kcs)

let aead_encrypt kcs key iv aad msg
  = EdhocCrypto.alg_aead_encrypt (get_aead_alg kcs) key iv aad msg

/// AEAD decryption
val aead_decrypt:
  kcs: supportedKemCipherSuite
  -> key: aead_key kcs
  -> iv: aead_iv
  -> aad: aead_valid_input kcs
  -> ciphertext: aead_valid_ciphertext kcs
  -> option (lbytes (Seq.length ciphertext - aead_tag_size kcs))

let aead_decrypt kcs key iv aad ciphertext
  = EdhocCrypto.alg_aead_decrypt (get_aead_alg kcs) key iv aad ciphertext

val lemma_aead_encryption_decryption_correctness:
  kcs: supportedKemCipherSuite
  -> key: aead_key kcs
  -> iv: aead_iv
  -> aad: aead_valid_input kcs
  -> msg: aead_valid_input kcs
  -> Lemma (ensures (
    let ciphertext = aead_encrypt kcs key iv aad msg in
    let decrypted_msg = aead_decrypt kcs key iv aad ciphertext in

    match decrypted_msg with
    | Some m -> Seq.equal m msg
    | None -> false
  ))
  [SMTPat (aead_encrypt kcs key iv aad msg)]

let lemma_aead_encryption_decryption_correctness kcs key iv aad msg
  = EdhocCrypto.alg_aead_correctness (get_aead_alg kcs) key iv aad msg

/// MAC23 size
// As KEMEDHOC does not use Signature so MAC size here is
// equal to the AEAD tag size
inline_for_extraction
let mac23_size (kcs: kemCipherSuite)
  = aead_tag_size kcs
inline_for_extraction
let mac23_byte (kcs: kemCipherSuite)
  = lbytes (mac23_size kcs)



(*----------- Hash function*)

/// Hash out type
inline_for_extraction
let hash_size (kcs: kemCipherSuite)
  = EdhocCrypto.alg_hash_size (get_hash_alg kcs)
inline_for_extraction
let hash_out (kcs: kemCipherSuite)
  = EdhocCrypto.alg_hash_out (get_hash_alg kcs)

let do_hash (kcs: supportedKemCipherSuite)
  (input: EdhocCrypto.valid_hash_input_bytes (get_hash_alg kcs))
  = EdhocCrypto.alg_do_hash (get_hash_alg kcs) input

(*----------- HMAC*)
val hkdf_extract:
  kcs: supportedKemCipherSuite
  -> salt: bytes
  -> ikm: bytes
  -> Pure (hash_out kcs)
  (requires (
    let a = get_hash_alg kcs in

    not (HashSpec.is_shake a)
    /\ Seq.length salt = EdhocCrypto.alg_hash_size a // needs to loose the restriction if possible
    /\ HKDFSpec.extract_ikm_length_pred a (Seq.length ikm)
  ))
  (ensures fun _ -> true)

let hkdf_extract kcs salt ikm
  = EdhocCrypto.alg_hkdf_extract (get_hash_alg kcs) salt ikm

val hkdf_expand:
  kcs: supportedKemCipherSuite
  -> prk:bytes
  -> info:bytes
  -> len:size_nat
  -> Pure (lbytes len)
  (requires (
    let a = get_hash_alg kcs in

    not (HashSpec.is_shake a)
    /\ Seq.length prk = EdhocCrypto.alg_hash_size a // needs to loose the restriction if possible
    /\ Seq.length info + HashSpec.block_length a + EdhocCrypto.alg_hash_size a
        < EdhocCrypto.alg_get_hash_max_input a
    /\ len <= 255 * EdhocCrypto.alg_hash_size a
  ))
  (ensures fun _ -> true)

let hkdf_expand kcs prk info len
  = EdhocCrypto.alg_hkdf_expand (get_hash_alg kcs) prk info len

(*----------- KEM types and algorithms*)

/// Utility types for KEM algorithms
inline_for_extraction
type kemPublicKey (kcs: kemCipherSuite) = lbytes (kem_public_key_size kcs)
inline_for_extraction
type kemPrivateKey (kcs: kemCipherSuite) = lbytes (kem_priv_key_size kcs)
inline_for_extraction
type kemCiphertext (kcs: kemCipherSuite) = lbytes (kem_ciphertext_size kcs)
inline_for_extraction
type kemSharedSecret (kcs: kemCipherSuite) = lbytes (kem_shared_secret_size kcs)

/// type `state` for randomization in KEM
inline_for_extraction
type kemState = FrodoRandomSpec.state_t
/// Assume the random state is globally available

/// KEM keypair type
type alg_kemKeyPair (a: kemAlg) = (lbytes (alg_kem_public_key_size a)) & (lbytes (alg_kem_priv_key_size a))
inline_for_extraction
type kemKeyPair (kcs:supportedKemCipherSuite) = alg_kemKeyPair (get_kem_alg kcs)
inline_for_extraction
let get_pub_kem_key (#kcs:supportedKemCipherSuite) (kp: kemKeyPair kcs)
  : kemPublicKey kcs
  = match kp with
    | pub, _ -> pub
inline_for_extraction
let get_priv_kem_key (#kcs:supportedKemCipherSuite) (kp: kemKeyPair kcs)
  : kemPrivateKey kcs
  = match kp with
    | _, priv -> priv

/// KEM Encapsulation output
type alg_kemEncapsOutput (a: kemAlg) = (lbytes (alg_kem_ciphertext_size a)) & (lbytes (alg_kem_shared_secret_size a))
inline_for_extraction
type kemEncapsOutput (kcs:supportedKemCipherSuite) =
  alg_kemEncapsOutput (get_kem_alg kcs)
inline_for_extraction
let get_kem_ciphertext (#kcs:supportedKemCipherSuite) (encaps: kemEncapsOutput kcs)
  : kemCiphertext kcs
  = match encaps with
    | ct, _ -> ct
inline_for_extraction
let get_kem_shared_secret (#kcs:supportedKemCipherSuite) (encaps: kemEncapsOutput kcs)
  : kemSharedSecret kcs
  = match encaps with
    | _, ss -> ss

(*Algorithm-driven KEM algorithm: KeyGen, Encaps, Decaps*)
/// KEM key generation
inline_for_extraction
let kem_entr_len = 48

val alg_kem_keygen:
  a: supportedKemAlg
  -> entr: entropy
  -> alg_kemKeyPair a

let alg_kem_keygen a entr
  = let entr1, kem_entr = crypto_random entr kem_entr_len in
  let state: kemState = FrodoRandomSpec.randombytes_init_ kem_entr in
  FrodoKemKeyGen.crypto_kem_keypair (kemAlg_to_frodo_alg a) genFrodoAlg state

/// KEM encapsulation
val alg_kem_encaps:
  a: supportedKemAlg
  -> entr: entropy
  -> pub_key: lbytes (alg_kem_public_key_size a)
  -> alg_kemEncapsOutput a

let alg_kem_encaps a entr pub_key
  = let entr1, kem_entr = crypto_random entr kem_entr_len in
  let state: kemState = FrodoRandomSpec.randombytes_init_ kem_entr in
  FrodoKemEncaps.crypto_kem_enc (kemAlg_to_frodo_alg a) genFrodoAlg state pub_key

/// KEM decapsulation
val alg_kem_decaps:
  a: supportedKemAlg
  -> ct: lbytes (alg_kem_ciphertext_size a)
  -> priv_key: lbytes (alg_kem_priv_key_size a)
  -> lbytes (alg_kem_shared_secret_size a)

let alg_kem_decaps a ct priv_key
  = FrodoKemDecaps.crypto_kem_dec (kemAlg_to_frodo_alg a) genFrodoAlg ct priv_key

(*Ciphersuite-driven KEM algorithms: KeyGen, Encaps, Decaps*)
/// KEM key generation
val kem_keygen:
  kcs: supportedKemCipherSuite
  -> entr: entropy
  -> kemKeyPair kcs

let kem_keygen kcs entr
  = alg_kem_keygen (get_kem_alg kcs) entr

/// KEM encapsulation
val kem_encaps:
  kcs: supportedKemCipherSuite
  -> entr: entropy
  -> pub_key: kemPublicKey kcs
  -> kemEncapsOutput kcs

let kem_encaps kcs entr pub_key
  = alg_kem_encaps (get_kem_alg kcs) entr pub_key

/// KEM decapsulation
val kem_decaps:
  kcs: supportedKemCipherSuite
  -> ct: kemCiphertext kcs
  -> priv_key: kemPrivateKey kcs
  -> kemSharedSecret kcs

let kem_decaps kcs ct priv_key
  = alg_kem_decaps (get_kem_alg kcs) ct priv_key

/// Lemmas for functional correctness of KEM
let lemma_alg_kem_functional_correctness
  (a: supportedKemAlg) (entr: entropy)
  : Lemma (ensures (
    let pub_key, priv_key = alg_kem_keygen a entr in
    let ct, ss = alg_kem_encaps a entr pub_key in
    let decaped_ss = alg_kem_decaps a ct priv_key in

    equal ss decaped_ss
  ))
  [SMTPat (alg_kem_keygen a entr)]
  = admit ()

let lemma_kem_functional_correctness
  (kcs: supportedKemCipherSuite) (entr: entropy)
  : Lemma (ensures (
    let pub_key, priv_key = kem_keygen kcs entr in
    let ct, ss = kem_encaps kcs entr pub_key in
    let decaped_ss = kem_decaps kcs ct priv_key in

    equal ss decaped_ss
  ))
  [SMTPat (kem_keygen kcs entr)]
  = lemma_alg_kem_functional_correctness (get_kem_alg kcs) entr