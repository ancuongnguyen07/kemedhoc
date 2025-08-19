module Spec.EDHOC.CryptoPrimitives

open Spec.EDHOC.Base.Definitions

module Seq = Lib.Sequence
module HACLRandom = Lib.RandomSequence


open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

(**
EDHOC implementation MUST supports cipher suite 2 and 3:
- 2: AES-CCM-16-64-128, SHA256, MAC len 8, P256, ES256
- 3: AES-CCM-16-128-128, SHA256, MAC len 16, P256, ES256
*)

(*
EDHOC supports variants of AES-CCM as follows:
- AES-CCM-16-64-128 (mandatory) (NOT supported by HACL)
- AES-CCM-16-128-128 (mandatory) (NOT supported by HACL)
- A128GCM
- A256GCM
- ChaCha20/Poly1305
*)
module AEAD = Spec.Agile.AEAD
open Spec.Agile.AEAD

(*
EDHOC supports variants of Hash as follows:
- SHA-256
- SHA-384
- SHAKE256
*)
module Hash = Spec.Hash.Definitions
open Spec.Agile.Hash
module HMACAgile = Spec.Agile.HMAC
module HKDF = Spec.Agile.HKDF
open Spec.Agile.HKDF
// module HMAC = Spec.Agile.HMAC
// open Spec.Agile.HMAC

(**
EDHOC supports variants of Elliptic curves for DH and signature as follows:
- P-256 | ES256
- X25519 | EdDSA
*)
module DH = Spec.Agile.DH
open Spec.Agile.DH

(**
EDHOC supports variants of ECDSA as follows:
- ES256
- EdDSA on X25519 curve
*)
/// There is no high-level spec of DSA alogrithms in HACL
/// it only supports specific implementation, so I create high-level types here
module P256 = Spec.P256
module Ed25519 = Spec.Ed25519
// type signatureAlg =
//   | ES256
//   | EdDSA25519

open Lib.ByteSequence
open FStar.Mul

let is_supported_dh_alg (a:DH.algorithm) : bool
  = match a with
    | DH_Curve25519 | DH_P256 -> true
    | _ -> false
type dhAlg = a:DH.algorithm{is_supported_dh_alg a}
inline_for_extraction
type signatureAlg = a:DH.algorithm{is_supported_dh_alg a}

// let is_supported_signature (a:signatureAlg) : bool
//   = match a with
//     | ES256 | EdDSA25519 -> true
//     | _ -> false

// let dhAlg_from_signatureAlg (a:signatureAlg)
//   :dhAlg
//   = match a with
//     | ES256 -> DH_P256
//     | EdDSA25519 -> DH_Curve25519

let is_supported_hash (a:Hash.hash_alg) : bool
  = match a with
    | SHA2_256 -> true
    | _ -> false
type hashAlg = a:Hash.hash_alg{is_supported_hash a}

let is_supported_aead_alg (a:AEAD.alg) : bool
  = match a with
    | AES128_GCM | AES256_GCM -> true
    | _ -> false
type aeadAlg = a:AEAD.alg{is_supported_aead_alg a}


/// Construct a cipher suite with record does not work
/// as the element has refinement type Type0, while record type
/// only allows Type. :((
// type cipherSuite: Type0 = {
//   aead: aeadAlg,
//   hash: hashAlg,
//   ecdh: dhAlg,
//   signature_scheme: signatureAlg
// }

inline_for_extraction
type cipherSuite = aeadAlg & hashAlg & dhAlg & signatureAlg
let does_cs_contain_shake (c:cipherSuite)
  = match c with
    | _, hash_alg, _ , _ -> (
      if (is_shake hash_alg)
      then true
      else false
    )

inline_for_extraction
let get_aead_alg (c:cipherSuite) : aeadAlg
  = match c with
    aead_alg, _, _, _ -> aead_alg
inline_for_extraction
let get_hash_alg (c:cipherSuite) : hashAlg
  = match c with
    _, hash_alg, _, _ -> hash_alg
inline_for_extraction
let get_ec_alg (c:cipherSuite) : dhAlg
  = match c with
    _, _, ec_alg, _ -> ec_alg
inline_for_extraction
let get_signature_alg (c:cipherSuite) : signatureAlg
  = match c with
    _, _, _, signature_alg -> signature_alg


let cipherSuite_label (c:cipherSuite) : (option nat)
  = match c with
    // | CHACHA20_POLY1305, SHA2_256, DH_Curve25519, DH_Curve25519 -> Some 4
    // | CHACHA20_POLY1305, SHA2_256, DH_P256, DH_P256 -> Some 5
    | AES128_GCM, SHA2_256, DH_Curve25519, DH_P256 -> Some 6
    // this ciphersuite is customized to do sanity check, non-standard
    | AES128_GCM, SHA2_256, DH_P256, DH_P256 -> Some 7
    | _, _, _, _ -> None

let is_supported_cipherSuite (c:cipherSuite) : bool
  = cipherSuite_label c <> None

type supported_cipherSuite = cs:cipherSuite{is_supported_cipherSuite cs}
type supported_cipherSuite_label = n:nat{n >= 6 /\ n <= 7}

let get_supportedCipherSuite_label (c:supported_cipherSuite)
  : supported_cipherSuite_label
  = match cipherSuite_label c with
    | Some label -> label

let get_cipherSuite (label:supported_cipherSuite_label)
  : supported_cipherSuite
  = match label with
      // | 4 -> (CHACHA20_POLY1305, SHA2_256, DH_Curve25519, DH_Curve25519)
      // | 5 -> (CHACHA20_POLY1305, SHA2_256, DH_P256, DH_P256)
      | 6 -> (AES128_GCM, SHA2_256, DH_Curve25519, DH_P256)
      // this ciphersuite is customized to do sanity check, non-standard
      | 7 -> (AES128_GCM, SHA2_256, DH_P256, DH_P256)

(*----------------------- Key-related types and constants *)
/// algorithm-dependent variables
inline_for_extraction
// `size_nat` is from Lib.IntTypes
let ec_priv_key_size (a:dhAlg): size_nat = DH.size_key a
inline_for_extraction
let ec_pub_key_size (a:dhAlg): size_nat = DH.size_public a
inline_for_extraction
let aead_key_size (a:aeadAlg): size_nat = AEAD.key_length a
inline_for_extraction
let aead_tag_size (a:aeadAlg): size_nat = AEAD.tag_length a
inline_for_extraction
let aead_cipher_max_size (cs:supported_cipherSuite): nat = AEAD.cipher_max_length (get_aead_alg cs)
// inline_for_extraction
// let alg_hash_size: size_nat = 32
/// Fixed types and constants
// both ECDH and KEM shared secret are 32-bytes
inline_for_extraction
let alg_shared_secret_size (a:dhAlg): size_nat = DH.size_public a
inline_for_extraction
let shared_secret_size (cs:supported_cipherSuite) = alg_shared_secret_size (get_ec_alg cs)
inline_for_extraction
let signature_size: size_nat = 64
inline_for_extraction
// MAC tag for AEAD encryption/decryption
// just an alias compliant to the EDHOC RFC
let mac_size (a:aeadAlg): size_nat = aead_tag_size a

inline_for_extraction
let aead_iv_size: size_nat = 12
type aead_iv = lbytes aead_iv_size

(*
Hash size should be algorithm-dependent set in the spec.
Regarding non-bounded hash function such as SHA3 and Shake families,
use the default 32 bytes instead which is a resonable number
in the resource-constrained environment.
*)
inline_for_extraction
let hash_default_size = 32
let alg_hash_size (a:hashAlg)
  = if (is_shake a)
    then 32
    else hash_length a
let hash_size (cs:supported_cipherSuite)
  = alg_hash_size (get_hash_alg cs)

type authentication_material =
  | Signature
  | MAC

let get_auth_material (party:party_enum) (method:method_enum)
  :authentication_material
  = match (party, method) with
      | (_, SigSig) | (Initiator, SigStat) | (Responder, StatSig) -> Signature
      | (_, StatStat) | (Initiator, StatSig) | (Responder, SigStat) -> MAC

// mac23_size used for MAC_2 and MAC_3 
let alg_mac23_size (hash_alg:hashAlg) (aead_alg:aeadAlg) (method:authentication_material)
  : size_nat
  = match method with
    | MAC -> mac_size aead_alg // mac-based or kem-based
    | Signature -> alg_hash_size hash_alg // signature 

let mac23_size (cs:supported_cipherSuite) (method:authentication_material)
  : size_nat
  = alg_mac23_size (get_hash_alg cs) (get_aead_alg cs) method

/// CryptoAlgorithm-dependent types
type alg_ec_priv_key (a:dhAlg) = lbytes (ec_priv_key_size a)
type alg_ec_pub_key (a:dhAlg) = lbytes (ec_pub_key_size a)
type alg_ec_signature_priv_key (a:signatureAlg) = alg_ec_priv_key a
type alg_ec_signature_pub_key (a:signatureAlg) = alg_ec_pub_key a
type alg_aead_key (a:aeadAlg) = lbytes (aead_key_size a)
type alg_aead_tag (a:aeadAlg) = lbytes (aead_tag_size a)
type alg_hash_out (a:hashAlg) = lbytes (alg_hash_size a)

/// CipherSuite-dependent types
type ec_priv_key (c:supported_cipherSuite) = alg_ec_priv_key (get_ec_alg c)
type ec_pub_key (c:supported_cipherSuite) = alg_ec_pub_key (get_ec_alg c)
type ec_signature_priv_key (c:supported_cipherSuite) = alg_ec_signature_priv_key (get_signature_alg c)
type ec_signature_pub_key (c:supported_cipherSuite) = alg_ec_signature_pub_key (get_signature_alg c)
type aead_key (c:supported_cipherSuite) = alg_aead_key (get_aead_alg c)
type aead_tag (c:supported_cipherSuite) = alg_aead_tag (get_aead_alg c)
type hash_out (c:supported_cipherSuite) = alg_hash_out (get_hash_alg c)

type shared_secret (c:supported_cipherSuite) = lbytes (shared_secret_size c)
inline_for_extraction
type mac23 (cs:supported_cipherSuite) (auth_material:authentication_material)
  = lbytes (mac23_size cs auth_material)

type ecdsa_signature = lbytes signature_size

let mac23_get_size (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (mac:mac23 cs auth_material)
  :size_nat
  = mac23_size cs auth_material

// val length_mac23:
//   #cs:supported_cipherSuite
//   -> #auth_material:authentication_material
//   -> mac:mac23 cs auth_material
//   -> Tot (n:size_nat{
//     n = hash_size cs
//     \/ n = mac_size (get_aead_alg cs)
//   })

// let get_mac23_bytes (#cs:supported_cipherSuite) (mac_either:mac23 cs)
//   :(b:bytes{let len_b = length b in
//             len_b = (hash_size cs) \/ len_b = (mac_size (get_aead_alg cs))})
//   = match mac_either with
//     | Inl lb -> lb
//     | Inr lb -> lb

// Only ECDH key sizes are considered in this file
// signature pub/priv key are embedded in Cert
noeq type ec_keypair (c:supported_cipherSuite) = {
  pub: ec_pub_key c;
  priv: ec_priv_key c
}

noeq type ec_signature_keypair (c:supported_cipherSuite) = {
  pub: ec_signature_pub_key c;
  priv: ec_signature_priv_key c
}

(*
The core idea here is to have two abstraction level: cipherSuite-driven
and CryptoAlg-driven. From the viewpoint of protocol, it manages messages
and states through cipherSuite level. Then in this CryptoPrimitve spec,
there should be a conversion from cipherSuite to CryptoAlg level.
CryptoAlg-driven functions are prefixed by `alg`.
*)

(*----------------- DH*)

/// private-to-public key derivation in EC, following the clamping rule

let alg_secret_to_public:
  #a:dhAlg
  -> priv:alg_ec_priv_key a
  -> Tot (option (alg_ec_pub_key a))
  = fun #a -> DH.secret_to_public a

let secret_to_public:
  #c:supported_cipherSuite
  -> ec_priv_key c
  -> Tot (option (ec_pub_key c))
  = fun #c -> alg_secret_to_public #(get_ec_alg c)

let lemma_secret_to_public_ed25519
  (#c:supported_cipherSuite)
  (priv:ec_priv_key c)
  : Lemma
  (ensures (
    let pk = (secret_to_public priv) in
    let ec_alg = get_ec_alg c in
    match ec_alg with
      | DH_Curve25519 -> Some?.v pk == Spec.Curve25519.secret_to_public priv
      | DH_P256 -> match pk with
                    | None -> true
                    | Some v -> v == Some?.v (Spec.P256.secret_to_public priv)
    )
  )
  [SMTPat (secret_to_public priv)]
  = ()

let alg_secret_to_public_signature_key:
  #a:signatureAlg
  -> alg_ec_signature_priv_key a
  -> Tot (option (alg_ec_signature_pub_key a))
  = fun #a -> DH.secret_to_public a

let secret_to_public_signature_key:
  #c:supported_cipherSuite
  -> ec_signature_priv_key c
  -> Tot (option (ec_signature_pub_key c))
  = fun #c -> alg_secret_to_public_signature_key #(get_signature_alg c)

let alg_dh:
  #a:dhAlg
  -> alg_ec_priv_key a
  -> alg_ec_pub_key a
  -> Tot (option (alg_ec_pub_key a))
  = fun #a -> DH.dh a

let dh:
  #c:supported_cipherSuite
  -> ec_priv_key c
  -> ec_pub_key c
  -> Tot (option (ec_pub_key c))
  = fun #c priv pub -> alg_dh #(get_ec_alg c) priv pub

#push-options "--max_fuel 8 --max_ifuel 8"
let lemma_dh_commutes
  (#c:supported_cipherSuite)
  (x:ec_priv_key c) (x_pub:ec_pub_key c)
  (r:ec_priv_key c) (r_pub:ec_pub_key c)
  : Lemma (requires (
    let g_x_op = secret_to_public x in
    let g_r_op = secret_to_public r in

    Option.isSome g_x_op /\ Option.isSome g_r_op
    /\ (
      let g_x = Some?.v g_x_op in
      let g_r = Some?.v g_r_op in

      let g_xr_op = dh r g_x in
      let g_rx_op = dh x g_r in

      Option.isSome g_xr_op /\ Option.isSome g_rx_op
      /\ lbytes_eq g_x x_pub /\ lbytes_eq g_r r_pub
  )))
  (ensures (
    let g_x = x_pub in
    let g_r = r_pub in

    let g_xr = Some?.v (dh r g_x) in
    let g_rx = Some?.v (dh x g_r) in

    lbytes_eq g_xr g_rx
  ))
  // [SMTPat (dh x r_pub)]
  = admit ()
#pop-options


(*----------------- AEAD*)
inline_for_extraction
let alg_aead_max_input_size (a:aeadAlg)
  = match a with
    | AES128_GCM | AES256_GCM -> pow2 31

inline_for_extraction
let aead_max_input_size (c:supported_cipherSuite) = alg_aead_max_input_size (get_aead_alg c)
inline_for_extraction
type valid_aead_input_bytes (c:supported_cipherSuite) = b:bytes{length b <= (aead_max_input_size c)}
type alg_aead_ciphertext_bytes (a:aeadAlg) = b:bytes{
  length b >= (aead_tag_size a)
  /\ length b <= AEAD.max_length a + (aead_tag_size a)
}
inline_for_extraction
type aead_ciphertext_bytes (c:supported_cipherSuite) = alg_aead_ciphertext_bytes (get_aead_alg c)

val alg_aead_encrypt:
  a:aeadAlg
  -> (alg_aead_key a)
  -> aead_iv
  -> aad:bytes{length aad <= alg_aead_max_input_size a}
  -> msg:bytes{length msg <= alg_aead_max_input_size a}
  -> Tot (r:bytes{length r = length msg + (aead_tag_size a)})

val lemma_alg_aead_encrypt_spec_aead_encrypt_equiv:
  a:aeadAlg
  -> key:alg_aead_key a
  -> iv:aead_iv
  -> aad:bytes{length aad <= alg_aead_max_input_size a}
  -> msg:bytes{length msg <= alg_aead_max_input_size a}
  -> Lemma (ensures alg_aead_encrypt a key iv aad msg
                  == AEAD.encrypt #a key iv aad msg)
  [SMTPat (alg_aead_encrypt a key iv aad msg)]

let aead_encrypt:
  #c:supported_cipherSuite
  -> aead_key c
  -> aead_iv
  -> aad:valid_aead_input_bytes c
  -> msg:valid_aead_input_bytes c
  -> Tot (r:bytes {length r = length msg + (aead_tag_size (get_aead_alg c))})
  = fun #c key iv aad msg -> alg_aead_encrypt (get_aead_alg c) key iv aad msg

val alg_aead_decrypt:
  a:aeadAlg
  -> alg_aead_key a
  -> aead_iv
  -> aad:bytes{length aad <= alg_aead_max_input_size a}
  -> ciphertext:alg_aead_ciphertext_bytes a
  -> Tot (option (r:lbytes (length ciphertext - (aead_tag_size a))))

val lemma_alg_aead_decrypt_spec_aead_decrypt_equiv:
  a:aeadAlg
  -> key:alg_aead_key a
  -> iv:aead_iv
  -> aad:bytes{length aad <= alg_aead_max_input_size a}
  -> ciphertext:alg_aead_ciphertext_bytes a
  -> Lemma (ensures alg_aead_decrypt a key iv aad ciphertext
                  == AEAD.decrypt #a key iv aad ciphertext)
  [SMTPat (alg_aead_decrypt a key iv aad ciphertext)]

let is_valid_cipher_length (c:supported_cipherSuite)
  (ciphertext:bytes)
  :bool
  = let ciphertext_len = length ciphertext in
  ciphertext_len >= aead_tag_size (get_aead_alg c)
    && ciphertext_len <= aead_max_input_size c + (aead_tag_size (get_aead_alg c))
     
let aead_decrypt:
  #c:supported_cipherSuite
  -> aead_key c
  -> aead_iv
  -> aad:valid_aead_input_bytes c
  -> ciphertext:aead_ciphertext_bytes c
  -> Tot (option (r:lbytes (length ciphertext - (aead_tag_size (get_aead_alg c)))))
  = fun #c key iv aad ciphertext -> alg_aead_decrypt (get_aead_alg c) key iv aad ciphertext


val alg_aead_correctness:
  a:aeadAlg
  -> k:alg_aead_key a
  -> iv:aead_iv
  -> aad:bytes{length aad <= alg_aead_max_input_size a}
  -> msg:bytes{length msg <= alg_aead_max_input_size a}
  -> Lemma (
    // Cannot prove this Lemma with equality due to typing issue.
    let ciphertext = alg_aead_encrypt a k iv aad msg in
    match alg_aead_decrypt a k iv aad ciphertext with
      | None -> false
      | Some msg' -> msg' == msg
  )

let aead_correctness:
  #c:supported_cipherSuite
  -> k:aead_key c
  -> iv:aead_iv
  -> aad:valid_aead_input_bytes c
  -> msg:valid_aead_input_bytes c
  -> Lemma (
    // Cannot prove this Lemma with equality due to typing issue.
    let ciphertext = aead_encrypt k iv aad msg in
    match aead_decrypt k iv aad ciphertext with
      | None -> false
      | Some msg' -> msg == msg'
  )
  = fun #c k iv aad msg -> alg_aead_correctness (get_aead_alg c) k iv aad msg


(*------------------- Hash*)
let alg_hash_max_input (a:hashAlg): option pos
  = Hash.max_input_length a

let alg_get_hash_max_input (a:hashAlg)
  = match (alg_hash_max_input a) with
    | None -> pow2 61 -1
    | Some v -> v

let get_hash_max_input (cs:supported_cipherSuite)
  = alg_get_hash_max_input (get_hash_alg cs)

val alg_do_hash:
  a:hashAlg
  -> input:bytes{length input <= alg_get_hash_max_input a}
  -> Tot (alg_hash_out a)

val lemma_alg_do_hash_spec_hash_equiv:
  a:hashAlg
  -> input:bytes
  -> Lemma (requires length input <= alg_get_hash_max_input a)
  (ensures alg_do_hash a input == hash a input)
  [SMTPat (alg_do_hash a input)]

let do_hash:
  c:supported_cipherSuite
  -> input:bytes{length input <= get_hash_max_input c}
  -> Tot (hash_out c)
  = fun c input -> alg_do_hash (get_hash_alg c) input


(*------------------- HMAC*)
val alg_hmac:
  a:hashAlg
  -> key:bytes
  -> data:bytes
  -> Pure (alg_hash_out a)
  (requires (
    not (is_shake a)
    /\ Seq.length key + Hash.block_length a < pow2 32
    /\ Seq.length data + Hash.block_length a < pow2 32
  ))
  (ensures fun _ -> true)

val lemma_alg_hmac_spec_hmac_equiv:
  a:hashAlg
  -> key:bytes
  -> data:bytes
  -> Lemma (requires (
    not (is_shake a)
    /\ Seq.length key + Hash.block_length a < pow2 32
    /\ Seq.length data + Hash.block_length a < pow2 32
  ))
  (ensures alg_hmac a key data == HMACAgile.hmac a key data)
  [SMTPat (alg_hmac a key data)]

let hmac:
  c:supported_cipherSuite
  -> key:bytes
  -> data:bytes
  -> Pure (hash_out c)
  (requires (
    let a = get_hash_alg c in
    not (is_shake a)
    /\ Seq.length key + Hash.block_length a < pow2 32
    /\ Seq.length data + Hash.block_length a < pow2 32
  ))
  (ensures fun _ -> true)
  = fun c key data -> alg_hmac (get_hash_alg c) key data


(*------------------- HKDF*)
/// HKDF_Expand needs to be separatedly defined here
/// to address differents purpose: iv_lenght, hash_length, key_length,
/// mac_length, and plaintext_length.
/// In EDHOC, only one-output HKDF is used, aka HKDF1.
/// It is used with different set of parameters, especially unique info.
val alg_hkdf_expand:
  a:hashAlg
  -> prk:bytes
  -> info:bytes
  -> len:size_nat
  -> Pure (lbytes len)
  (requires (
    not (is_shake a)
    /\ Seq.length prk = alg_hash_size a // needs to loose the restriction if possible
    /\ Seq.length info + Hash.block_length a + alg_hash_size a
        < alg_get_hash_max_input a
    /\ len <= 255 * alg_hash_size a
  ))
  (ensures fun _ -> true)

val lemma_alg_hkdf_expand_spec_expand_equiv:
  a:hashAlg
  -> prk:bytes
  -> info:bytes
  -> len:size_nat
  -> Lemma (requires (
    not (is_shake a)
    /\ Seq.length prk = alg_hash_size a // needs to loose the restriction if possible
    /\ expand_info_length_pred a (Seq.length info)
    /\ expand_output_length_pred a len
  ))
  (ensures alg_hkdf_expand a prk info len == expand a prk info len)
  [SMTPat (alg_hkdf_expand a prk info len)]

let hkdf_expand:
  c:supported_cipherSuite
  -> prk:bytes
  -> info:bytes
  -> len:size_nat
  -> Pure (lbytes len)
  (requires (
    let a = get_hash_alg c in
    not (does_cs_contain_shake c)
    /\ Seq.length prk = alg_hash_size a // needs to loose the restriction if possible
    /\ expand_info_length_pred a (Seq.length info)
    /\ expand_output_length_pred a len
  ))
  (ensures fun _ -> true)
  = fun c prk info len -> alg_hkdf_expand (get_hash_alg c) prk info len

/// HKDF_Extract is basically HMAC using salt as key and the IKM as text.
/// No need for separate definement as they serve only one purpose
/// is to derive PRK.
val alg_hkdf_extract:
  a:hashAlg
  -> salt:bytes // salt
  -> ikm:bytes // IKM
  -> Pure (alg_hash_out a)
  (requires (
    not (is_shake a)
    /\ Seq.length salt = alg_hash_size a // needs to loose the restriction if possible
    /\ extract_ikm_length_pred a (Seq.length ikm)
  ))
  (ensures fun _ -> true)

val lemma_alg_hkdf_extract_spec_extract_equiv:
  a:hashAlg
  -> salt:bytes
  -> ikm:bytes
  -> Lemma (requires (
    not (is_shake a)
    /\ Seq.length salt = alg_hash_size a // needs to loose the restriction if possible
    /\ extract_ikm_length_pred a (Seq.length ikm)
  ))
  (ensures alg_hkdf_extract a salt ikm == extract a salt ikm)
  [SMTPat (alg_hkdf_extract a salt ikm)]

let hkdf_extract:
  c:supported_cipherSuite
  -> salt:bytes
  -> ikm:bytes
  -> Pure (hash_out c)
  (requires (
    let a = get_hash_alg c in
    not (does_cs_contain_shake c)
    /\ Seq.length salt = alg_hash_size a // needs to loose the restriction if possible
    /\ extract_ikm_length_pred a (Seq.length ikm)
  ))
  (ensures fun _ -> true) 
  = fun c salt ikm -> alg_hkdf_extract (get_hash_alg c) salt ikm

(*------------------------ EC signature scheme*)
inline_for_extraction
let nonceP256_size = 32
type nonceP256 = lbytes nonceP256_size

// let lseq_to_lbytes (#a:Type0) (#len:size_nat) (ls: (lseq a len))
//   : lbytes_l SEC len = lseq (uint_t U8 SEC) len 

(*split_signature is only needed for ES256*)
let split_signature (sig:ecdsa_signature)
  : (lbytes 32 & lbytes 32) =
    let r = Seq.sub #_ #64 sig 0 32 in
    let s = Seq.sub #_ #64 sig 32 32 in
    (r, s)

let lemma_split_signature_equiv
  (sig:ecdsa_signature)
  :Lemma (ensures (
    let (r,s) = split_signature sig in
    Seq.equal sig (Seq.concat r s)
  ))
  [SMTPat (split_signature sig)]
  = ()

/// EC-Signing
val alg_ecdsa_sign:
  a:signatureAlg
  -> ha:hashAlg
  -> op_nonce:option (lbytes 32)
  -> msg:bytes
  -> priv_key:alg_ec_signature_priv_key a
  -> Pure (option ecdsa_signature)
  (requires (
    let msg_len = length msg in
    msg_len >= P256.min_input_length (P256.Hash ha)
    /\ msg_len <= max_size_t
  ) /\ (
    match a with
      | DH_P256 -> Some? op_nonce
      | DH_Curve25519 -> not (Some? op_nonce)
  ))
  (ensures fun _ -> true)

val lemma_alg_ecdsa_sign_ed25519_returns_Some:
  ha:hashAlg
  -> op_nonce:option (lbytes 32)
  -> msg:bytes
  -> priv_key:alg_ec_signature_priv_key DH_Curve25519
  -> Lemma (requires (
    let msg_len = length msg in
    msg_len >= P256.min_input_length (P256.Hash ha)
    /\ msg_len <= max_size_t
  ) /\ not (Some? op_nonce)
  )
  (ensures (
    let res = (alg_ecdsa_sign DH_Curve25519 ha op_nonce msg priv_key) in
    match res with
      | None -> false
      | Some v -> v == Spec.Ed25519.sign priv_key msg
  ))
  [SMTPat (alg_ecdsa_sign DH_Curve25519 ha op_nonce msg priv_key)]

val lemma_alg_ecdsa_sign_p256_returns_option:
  ha:hashAlg
  -> op_nonce:option (lbytes 32)
  -> msg:bytes
  -> priv_key:alg_ec_signature_priv_key DH_P256
  -> Lemma (requires (
    let msg_len = length msg in
    msg_len >= P256.min_input_length (P256.Hash ha)
    /\ msg_len <= max_size_t
  ) /\ Some? op_nonce
  )
  (ensures (
    let agile_res = alg_ecdsa_sign DH_P256 ha op_nonce msg priv_key in
    let msg_len = length msg in
    let spec_res = P256.ecdsa_signature_agile (P256.Hash ha) msg_len msg priv_key (Some?.v op_nonce) in
    match (agile_res, spec_res) with
      | None, None -> True
      | Some v1, Some v2 -> v1 == v2
      | _ -> False
  ))
  [SMTPat (alg_ecdsa_sign DH_P256 ha op_nonce msg priv_key)]

let ecdsa_sign:
  #c:supported_cipherSuite
  -> op_nonce:option (lbytes 32)
  -> msg:bytes
  -> priv_key:ec_signature_priv_key c
  -> Pure (option ecdsa_signature)
  (requires (
    let ha: hashAlg = get_hash_alg c in
    let msg_len = length msg in
    msg_len >= P256.min_input_length (P256.Hash ha)
    /\ msg_len <= max_size_t
  ) /\ (
    match (get_signature_alg c) with
      | DH_P256 -> Some? op_nonce
      | DH_Curve25519 -> not (Some? op_nonce)
  ))
  (ensures fun _ -> true)
  = fun #c op_nonce msg priv_key -> alg_ecdsa_sign (get_signature_alg c) (get_hash_alg c) op_nonce msg priv_key 

/// EC-Verification
val alg_ecdsa_verify:
  a:signatureAlg
  -> ha:hashAlg
  -> msg:bytes{
    let msg_len = length msg in
    msg_len >= P256.min_input_length (P256.Hash ha)
    /\ msg_len <= max_size_t
  }
  -> pub_key:alg_ec_signature_pub_key a
  -> signature:ecdsa_signature
  -> bool

val lemma_alg_ecdsa_verify_p256_spec_equiv:
  ha:hashAlg
  -> msg:bytes
  -> pub_key:alg_ec_signature_pub_key DH_P256
  -> signature:ecdsa_signature
  -> Lemma (requires (
    let msg_len = length msg in
    msg_len >= P256.min_input_length (P256.Hash ha)
    /\ msg_len <= max_size_t
  ))
  (ensures (
    let msg_len = length msg in
    let (sig_r, sig_s) = split_signature signature in
    let agile_res = alg_ecdsa_verify DH_P256 ha msg pub_key signature in
    let spec_res = P256.ecdsa_verification_agile (P256.Hash ha) msg_len msg pub_key sig_r sig_s in
    agile_res == spec_res
  ))
  [SMTPat (alg_ecdsa_verify DH_P256 ha msg pub_key signature)]

val lemma_alg_ecdsa_verify_ed25519_spec_equiv:
  ha:hashAlg
  -> msg:bytes
  -> pub_key:alg_ec_signature_pub_key DH_Curve25519
  -> signature:ecdsa_signature
  -> Lemma (requires (
    let msg_len = length msg in
    msg_len >= P256.min_input_length (P256.Hash ha)
    /\ msg_len <= max_size_t
  ))
  (ensures (
    let agile_res = alg_ecdsa_verify DH_Curve25519 ha msg pub_key signature in
    let spec_res = Ed25519.verify pub_key msg signature in
    agile_res == spec_res
  ))
  [SMTPat (alg_ecdsa_verify DH_Curve25519 ha msg pub_key signature)]

let ecdsa_verify:
  #c:supported_cipherSuite
  -> msg:bytes{
    let ha: hashAlg = get_hash_alg c in
    let msg_len = length msg in
    msg_len >= P256.min_input_length (P256.Hash ha)
    /\ msg_len <= max_size_t
  }
  -> pub_key:ec_signature_pub_key c
  -> signature: ecdsa_signature
  -> bool
  = fun #c msg pub_key signature -> alg_ecdsa_verify (get_signature_alg c) (get_hash_alg c) msg pub_key signature

(*----------------------- Stream Cipher XOR*)
val xor:
  #len:size_nat
  -> b1:lbytes len
  -> b2:lbytes len
  -> lbytes len

val lemma_xor_map2_logxor_equiv:
  #len:size_nat
  -> b1:lbytes len
  -> b2:lbytes len
  -> Lemma (ensures xor b1 b2 == Seq.map2 (logxor #U8 #SEC) b1 b2)
  [SMTPat (xor #len b1 b2)]

let lemma_xor_interchange
  (#len:size_nat) (b1:lbytes len) (b2:lbytes len)
  : Lemma (ensures xor b1 b2 == xor b2 b1)
  [SMTPat (xor #len b1 b2)]
  = admit()

val lemma_xor_involution:
  #len:size_nat
  -> b1:lbytes len
  -> b2:lbytes len
  -> Lemma
  (ensures (
    let result = xor b1 b2 in
    lbytes_eq (xor result b1) b2
  ))
  [SMTPat (xor #len b1 b2)]

(*--------------------- Generate key pairs*)
/// Assume an entropy

val construct_ec_keypair:
  #cs:supported_cipherSuite
  -> ec_priv_key cs
  -> option (ec_keypair cs)

val lemma_construct_ec_keypair_equiv:
  #cs:supported_cipherSuite
  -> sk:ec_priv_key cs
  -> Lemma (ensures (
    let pk_opt = secret_to_public sk in
    match construct_ec_keypair sk with
      | None -> pk_opt == None
      | Some kp -> pk_opt == Some kp.pub /\ kp.priv == sk
  ))
  [SMTPat (construct_ec_keypair sk)]

/// Generate EC key pair: x and g^x
val generate_ec_keypair:
  cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> Tot (option (ec_keypair cs & HACLRandom.entropy))

val lemma_generate_ec_keypair_some_secret_to_public:
  cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> Lemma (ensures (
    let (e1, sk)
      = HACLRandom.crypto_random entr (ec_priv_key_size (get_ec_alg cs)) in

    let keypair_op = construct_ec_keypair sk in
    let pk_op = secret_to_public sk in
    match keypair_op with
      | None -> pk_op == None
      | Some kp -> kp.priv == sk /\ kp.pub == (Some?.v pk_op)
  ))

/// Generate signature key pair
val generate_ec_signature_keypair:
  cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> Tot (option (ec_signature_keypair cs & HACLRandom.entropy))
