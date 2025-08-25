module Spec.KEMEDHOC.KeySchedule

module Seq = Lib.Sequence
open Lib.IntTypes
open Lib.ByteSequence

open Spec.KEMEDHOC.CryptoPrimitives
open Spec.KEMEDHOC.Parser

open Spec.EDHOC.Serialization
module EdhocParser = Spec.EDHOC.Parser

module FBytes = FStar.Bytes

(*-------------------- Key deriviation info constants*)
type info_label = n:nat{n <= 13}

inline_for_extraction
let info_label_k1 = 0
inline_for_extraction
let info_label_iv1 = 1
inline_for_extraction
let info_label_k2 = 2
inline_for_extraction
let info_label_iv2 = 3
inline_for_extraction
let info_label_salt3e2m = 4
inline_for_extraction
let info_label_mac2 = 5
inline_for_extraction
let info_label_k3 = 6
inline_for_extraction
let info_label_iv3 = 7
inline_for_extraction
let info_label_salt4e3m = 8
inline_for_extraction
let info_label_mac3 = 9
inline_for_extraction
let info_label_prk_out = 10
inline_for_extraction
let info_label_k4 = 11
inline_for_extraction
let info_label_iv4 = 12
inline_for_extraction
let info_label_prk_exporter = 13

/// Inherited types from EDHOC parser

(*---------------------------- HKDF Info*)

unopteq type info = {
  label: info_label;
  context: serializable_bytes;
  // okem_len is actual field of info
  // not a length-noticed field like context_len
  okm_len: EdhocParser.okm_len_type;
}

val construct_info:
  label: info_label
  -> context: serializable_bytes
  -> okm_len: EdhocParser.okm_len_type
  -> Tot info

inline_for_extraction
let concat_info_get_length (i: info)
  : size_nat
  = (FBytes.repr_bytes i.label)
    + (Seq.length i.context)
    + (FBytes.repr_bytes i.okm_len)

val concat_info:
  i: info
  -> Tot (lbytes (concat_info_get_length i))

val lemma_concat_info_correctness:
  i: info
  -> Lemma (ensures (
    let label_len = FBytes.repr_bytes i.label in
    let context_len = Seq.length i.context in
    let okm_len = FBytes.repr_bytes i.okm_len in
    let concatenated_info = concat_info i in

    Seq.equal (nat_to_bytes i.label) (Seq.sub concatenated_info 0 label_len)
    /\ Seq.equal i.context (Seq.sub concatenated_info label_len context_len)
    /\ Seq.equal (nat_to_bytes i.okm_len) (Seq.sub concatenated_info (label_len + context_len) okm_len)
  ))
  [SMTPat (concat_info i)]

(*---------------------------- HKDF context*)

/// ---------------
/// Context 2
/// ---------------

unopteq type context2 (#kcs: supportedKemCipherSuite) = {
  c_r: c_id_byte;
  id_cred_r: id_cred_byte;
  // the length of th2 must be typed as `hash_out cs`
  th2: hash_out kcs;
  cred_r: cred_byte;
  // Does not support EAD2
  // ead2:option ead_bytes;
}

let construct_context2 (#kcs: supportedKemCipherSuite)
  (c_r: c_id_byte) (id_cred_r: id_cred_byte)
  (th2: hash_out kcs) (cred_r: cred_byte)
  // ead2 is an optional field
  = {
    c_r = c_r;
    id_cred_r = id_cred_r;
    th2 = th2;
    cred_r = cred_r;
    // ead2 is not supported in this context
  }

let concat_context2_get_length (#kcs: supportedKemCipherSuite)
  (ctx: context2 #kcs)
  : size_nat
  = Seq.length ctx.c_r + Seq.length ctx.id_cred_r
    + Seq.length ctx.th2 + Seq.length ctx.cred_r

val concat_context2:
  #kcs: supportedKemCipherSuite
  -> ctx2: context2 #kcs
  -> lbytes (concat_context2_get_length ctx2)

val lemma_concat_context2_correctness:
  #kcs: supportedKemCipherSuite
  -> ctx2: context2 #kcs
  -> Lemma (ensures (
    let concatenated_ctx2 = concat_context2 ctx2 in

    Seq.equal (ctx2.c_r) (Seq.sub concatenated_ctx2 0 c_id_size)
    /\ Seq.equal ctx2.id_cred_r (Seq.sub concatenated_ctx2 c_id_size id_cred_size)
    /\ Seq.equal ctx2.th2 (Seq.sub concatenated_ctx2 (c_id_size + id_cred_size) (hash_size kcs))
    /\ Seq.equal ctx2.cred_r (Seq.sub concatenated_ctx2 (c_id_size + id_cred_size + hash_size kcs) cred_size)
  ))
  [SMTPat (concat_context2 #kcs ctx2)]

/// ---------------
/// Context 3
/// ---------------

unopteq type context3 (#kcs: supportedKemCipherSuite) = {
  id_cred_i: id_cred_byte;
  // the length of th3 must be typed as `hash_out cs`
  th3: hash_out kcs;
  cred_i: cred_byte;
  // Does not support EAD3
  // ead3:option ead_bytes;
}

let construct_context3 (#kcs: supportedKemCipherSuite)
  (id_cred_i: id_cred_byte) (th3: hash_out kcs) (cred_i: cred_byte)
  // ead3 is an optional field
  = {
    id_cred_i = id_cred_i;
    th3 = th3;
    cred_i = cred_i;
    // ead3 is not supported in this context
  }

let concat_context3_get_length (#kcs: supportedKemCipherSuite)
  (ctx: context3 #kcs)
  : size_nat
  = Seq.length ctx.id_cred_i + Seq.length ctx.th3
    + Seq.length ctx.cred_i

val concat_context3:
  #kcs: supportedKemCipherSuite
  -> ctx3: context3 #kcs
  -> lbytes (concat_context3_get_length ctx3)

val lemma_concat_context3_correctness:
  #kcs: supportedKemCipherSuite
  -> ctx3: context3 #kcs
  -> Lemma (ensures (
    let concatenated_ctx3 = concat_context3 ctx3 in

    Seq.equal ctx3.id_cred_i (Seq.sub concatenated_ctx3 0 id_cred_size)
    /\ Seq.equal ctx3.th3 (Seq.sub concatenated_ctx3 id_cred_size (hash_size kcs))
    /\ Seq.equal ctx3.cred_i (Seq.sub concatenated_ctx3 (id_cred_size + hash_size kcs) cred_size)
  ))
  [SMTPat (concat_context3 #kcs ctx3)]

(*---------------------------- HKDF key schedule*)

/// ---------------
/// PRK
/// ---------------

/// PRK1e = HKDF_Extract(TH1, K_auth_R)
val extract_prk1e:
  #kcs: supportedKemCipherSuite
  -> th1: hash_out kcs // salt
  -> k_auth_R: kemSharedSecret kcs // ikm
  -> hash_out kcs

/// PRK2e = HKDF_Extract(H(PRK1e, TH2), K_XY)
val extract_prk2e:
  #kcs: supportedKemCipherSuite
  -> prk1e: hash_out kcs
  -> th2: hash_out kcs // salt = H(prk1e || th2)
  -> k_xy: kemSharedSecret kcs // ikm
  -> hash_out kcs

/// PRK3e2m = HKDF_Extract(SALT3e2m, K_auth_R)
val extract_prk3e2m:
  #kcs: supportedKemCipherSuite
  -> salt3e2m: hash_out kcs // salt
  -> k_auth_R: kemSharedSecret kcs // ikm
  -> hash_out kcs

/// PRK4e3m = HKDF_Extract(SALT4e3m, K_auth_I)
val extract_prk4e3m:
  #kcs: supportedKemCipherSuite
  -> salt4e3m: hash_out kcs // salt
  -> k_auth_I: kemSharedSecret kcs // ikm
  -> hash_out kcs

/// PRK_out = HKDF_Expand(PRK4e3m, (10, TH4, hash_length), hash_length)
val expand_prk_out:
  #kcs: supportedKemCipherSuite
  -> prk4e3m: hash_out kcs // key
  -> th4: hash_out kcs // info
  -> hash_out kcs

/// PRK_exporter = HKDF_Expand(PRK4e3m, (13, empty_str, hash_length), hash_length)
val expand_prk_exporter:
  #kcs: supportedKemCipherSuite
  -> prk_out: hash_out kcs // key
  -> hash_out kcs

/// ---------------
/// Encryption Key
/// ---------------

val expand_k1:
  #kcs: supportedKemCipherSuite
  -> prk1e: hash_out kcs
  -> th1: hash_out kcs
  -> aead_key kcs

val expand_k2:
  #kcs: supportedKemCipherSuite
  -> prk2e: hash_out kcs
  -> th2: hash_out kcs
  -> aead_key kcs

val expand_k3:
  #kcs: supportedKemCipherSuite
  -> prk3e2m: hash_out kcs
  -> th3: hash_out kcs
  -> aead_key kcs

val expand_k4:
  #kcs: supportedKemCipherSuite
  -> prk4e3m: hash_out kcs
  -> th4: hash_out kcs
  -> aead_key kcs

/// ---------------
/// Initial Vector
/// ---------------

val expand_iv1:
  #kcs: supportedKemCipherSuite
  -> prk1e: hash_out kcs
  -> th1: hash_out kcs
  -> aead_iv

val expand_iv2:
  #kcs: supportedKemCipherSuite
  -> prk2e: hash_out kcs
  -> th2: hash_out kcs
  -> aead_iv

val expand_iv3:
  #kcs: supportedKemCipherSuite
  -> prk3e2m: hash_out kcs
  -> th3: hash_out kcs
  -> aead_iv

val expand_iv4:
  #kcs: supportedKemCipherSuite
  -> prk4e3m: hash_out kcs
  -> th4: hash_out kcs
  -> aead_iv

/// ---------------
/// SALT
/// ---------------

val expand_salt3e2m:
  #kcs: supportedKemCipherSuite
  -> prk2e: hash_out kcs
  -> th2: hash_out kcs
  -> hash_out kcs

val expand_salt4e3m:
  #kcs: supportedKemCipherSuite
  -> prk3e2m: hash_out kcs
  -> th3: hash_out kcs
  -> hash_out kcs

/// ---------------
/// MAC
/// ---------------

val expand_mac2:
  #kcs: supportedKemCipherSuite
  -> prk3e2m: hash_out kcs
  -> ctx2: context2 #kcs
  -> mac23_byte kcs

val expand_mac3:
  #kcs: supportedKemCipherSuite
  -> prk4e3m: hash_out kcs
  -> ctx3: context3 #kcs
  -> mac23_byte kcs