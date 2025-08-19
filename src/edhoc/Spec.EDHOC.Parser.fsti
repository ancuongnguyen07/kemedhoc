module Spec.EDHOC.Parser

module FBytes = FStar.Bytes

open FStar.Mul
open FStar.Pervasives

(*HACL libs*)
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

module Seq = Lib.Sequence

open Spec.EDHOC.Base.Definitions
open Spec.EDHOC.CryptoPrimitives
open Spec.EDHOC.Serialization
open Spec.EDHOC.CommonPred

// constants for max size
inline_for_extraction
let c_id_size = 2
inline_for_extraction
let id_cred_size = 400
inline_for_extraction
let cred_size = 400
inline_for_extraction
let sig_or_mac_max_size = 64
inline_for_extraction
let okm_len_max_size = 8160 // 255 * 32 maximum length of EDHOC_KDF output


///
/// NOTE!!! Currently this implementation does not support EAD
///
inline_for_extraction
let ead_max_size = 0

// needs to be refactored to get more flexible size for EAD2
inline_for_extraction
let plaintext2_max_size = c_id_size + id_cred_size
                          + signature_size + ead_max_size
inline_for_extraction
let plaintext3_max_size = id_cred_size + signature_size + ead_max_size

// max-fixed-length bytes
inline_for_extraction
type c_id_bytes = lbytes c_id_size
inline_for_extraction
type id_cred_i_bytes = lbytes id_cred_size
inline_for_extraction
type cred_i_bytes = lbytes cred_size
inline_for_extraction
type info_label = n:nat{n <= 12}
inline_for_extraction
type okm_len_type = n:size_nat{n <= okm_len_max_size}
// currently this specification does not support ead for
// easier to formally prove.
inline_for_extraction
type ead_bytes = b:serializable_bytes{length b <= ead_max_size}

/// Sig_or_MAC23 utilities
let sig_or_mac23_size (cs:supported_cipherSuite) (auth_material:authentication_material)
  = match auth_material with
    | Signature -> signature_size
    | MAC -> mac23_size cs auth_material

let lemma_sig_or_mac23_size
  (cs:supported_cipherSuite) (auth_material:authentication_material)
  :Lemma (ensures (
    let s = sig_or_mac23_size cs auth_material in
    (s = signature_size \/ s = mac_size (get_aead_alg cs) \/ s = hash_size cs)
    /\ (match auth_material with
        | Signature -> s = signature_size
        | MAC -> s = mac23_size cs auth_material
    )
  ))
  [SMTPat (sig_or_mac23_size cs auth_material)]
  = ()

type sig_or_mac23_bytes (cs:supported_cipherSuite) (auth_material:authentication_material)
  // = either ecdsa_signature (mac23 cs auth_material)
  = lbytes (sig_or_mac23_size cs auth_material)

// size of raw bytes ptx2 without ead2
let min_ptx2_size (cs:supported_cipherSuite) (auth_material:authentication_material)
  :size_nat
  = c_id_size + id_cred_size + sig_or_mac23_size cs auth_material

/// Plaintext2 length conditions
inline_for_extraction
let is_valid_ptx2_cipher2_size (cs:supported_cipherSuite)
  (auth_material:authentication_material) (len:size_nat)
  = len >= min_ptx2_size cs auth_material
    && len <= plaintext2_max_size && len <= okm_len_max_size
  
inline_for_extraction
type ptxt2_ctxt2_size (cs:supported_cipherSuite)
  (auth_material:authentication_material)
  = s:size_nat{is_valid_ptx2_cipher2_size cs auth_material s}

// ciphertext2 is a XOR product of plaintext2 so their length must be equal
inline_for_extraction
type ciphertext2_bytes (cs:supported_cipherSuite)
  (auth_material:authentication_material)
  = b:serializable_bytes{is_valid_ptx2_cipher2_size cs auth_material (length b)}
  
inline_for_extraction
type plaintext2_bytes (cs:supported_cipherSuite)
  (auth_material:authentication_material)
  = ciphertext2_bytes cs auth_material


/// Plaintext3 length conditions
// size of raw bytes ptx3 without ead3
inline_for_extraction
let min_ptx3_size (cs:supported_cipherSuite) (auth_material:authentication_material)
  :size_nat
  = id_cred_size + sig_or_mac23_size cs auth_material

inline_for_extraction
let is_valid_ptx3_size (cs:supported_cipherSuite)
  (auth_material:authentication_material) (len:size_nat)
  = len >= min_ptx3_size cs auth_material
  && len <= plaintext3_max_size
  && len <= okm_len_max_size

inline_for_extraction
type plaintext3_size (cs:supported_cipherSuite)
  (auth_material:authentication_material)
  = s:size_nat{is_valid_ptx3_size cs auth_material s}

inline_for_extraction
type plaintext3_bytes (cs:supported_cipherSuite)
  (auth_material:authentication_material)
  = b:serializable_bytes{is_valid_ptx3_size cs auth_material (length b)}

// val sig_or_mac23_get_length:
//   #cs:supported_cipherSuite
//   -> #auth_material:authentication_material
//   -> sig_or_mac23_bytes #cs #auth_material
//   -> Tot size_nat
val sig_or_mac23_get_length:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> sig_or_mac23_bytes cs auth_material
  -> s:size_nat{s = sig_or_mac23_size cs auth_material}

// val sig_or_mac23_get_bytes:
//   #cs:supported_cipherSuite
//   -> #auth_material:authentication_material
//   -> sig_or_mac23_bytes #cs #auth_material
//   -> Tot bytes

// val is_valid_sig_or_mac23_length:
//   cs:supported_cipherSuite
//   -> auth_material:authentication_material
//   -> n:nat
//   -> Tot bool

// val bytes_to_sig_or_mac23_bytes:
//   cs:supported_cipherSuite
//   -> auth_material:authentication_material
//   -> raw_bytes:bytes
//   -> Tot (option (sig_or_mac23_bytes #cs #auth_material))

/// Sig_or_MAC23 lemmas
// val lemma_sig_or_mac23_valid_length:
//   #cs:supported_cipherSuite
//   -> #auth_material:authentication_material
//   -> sig_or_mac:sig_or_mac23_bytes #cs #auth_material
//   -> Lemma (ensures (
//     let len_b = sig_or_mac23_get_length sig_or_mac in
//     len_b = signature_size
//     \/ len_b = mac_size (get_aead_alg cs)
//   ))

unopteq type info = {
  label:info_label;
  context:serializable_bytes;
  // okem_len is actual field of info
  // not a length-noticed field like context_len
  okm_len:okm_len_type;
}

unopteq type context2 (#cs:supported_cipherSuite) = {
  c_r:c_id_bytes;
  id_cred_r:id_cred_i_bytes;
  // the length of th2 must be typed as `hash_out cs`
  th2:hash_out cs;
  cred_r:cred_i_bytes;
  ead2:option ead_bytes;
}

unopteq type context3 (#cs:supported_cipherSuite) = {
  id_cred_i:id_cred_i_bytes;
  // the length of th3 must be typed as `hash_out cs`
  th3:hash_out cs;
  cred_i:cred_i_bytes;
  ead3:option ead_bytes;
}

(*---------------------------- Message 1*)
unopteq type message1 (#cs:supported_cipherSuite) = {
  method: method_enum;
  suite_i: supported_cipherSuite_label;
  g_x: ec_pub_key cs;
  c_i: c_id_bytes;
  ead1: option ead_bytes
}

let message1_compare (#cs:supported_cipherSuite)
  (msgA:message1 #cs) (msgB:message1 #cs)
  : Type0
  = msgA.method == msgB.method
  /\ msgA.suite_i = msgB.suite_i
  /\ Seq.equal (msgA.g_x) (msgB.g_x)
  /\ Seq.equal (msgA.c_i) (msgB.c_i)
  /\ (Some? msgA.ead1 <==> Some? msgB.ead1)
  /\ (Some? msgA.ead1 ==> (
    let ead1_A = Some?.v msgA.ead1 in
    let ead1_B = Some?.v msgB.ead1 in
    unequal_lbytes_eq (ead1_A <: lbytes (length ead1_A)) (ead1_B <: lbytes (length ead1_B))
  ))

(*---------------------------- Plaintext 2*)
unopteq type plaintext2 (#cs:supported_cipherSuite) (#auth_material:authentication_material) = {
  c_r: c_id_bytes;
  id_cred_r: id_cred_i_bytes;
  sig_or_mac2: sig_or_mac23_bytes cs auth_material;
  ead2:option ead_bytes
}

(*---------------------------- Message 2*)
unopteq type message2 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  = {
  g_y: ec_pub_key cs; // Needs to be modified if KEM is integrated
  ciphertext2: ciphertext2_bytes cs auth_material
}

let message2_compare (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (msgA:message2 #cs #auth_material) (msgB:message2 #cs #auth_material)
  = Seq.equal (msgA.g_y) msgB.g_y
  /\ unequal_lbytes_eq (msgA.ciphertext2 <: lbytes (length msgA.ciphertext2))
    (msgB.ciphertext2 <: lbytes (length msgB.ciphertext2))

(*---------------------------- Plaintext 3*)
unopteq type plaintext3 (#cs:supported_cipherSuite) (#auth_material:authentication_material) = {
  id_cred_i:id_cred_i_bytes;
  sig_or_mac3:sig_or_mac23_bytes cs auth_material;
  ead3:option ead_bytes
}

(*---------------------------- Message 3*)
type message3 (#cs:supported_cipherSuite) = aead_ciphertext_bytes cs

(*--------------------------------------*)
(*---------------------------- Parsing*)
(*--------------------------------------*)

/// ------------------------
/// Message 1
/// ------------------------

// val concat_msg1_get_length:
//   #cs:supported_cipherSuite
//   -> msg1:message1 #cs
//   -> Tot size_nat

let concat_msg1_get_length (#cs:supported_cipherSuite)
  (msg1:message1 #cs)
  = let ead_len = match msg1.ead1 with
          | None -> 0
          | Some ead1 -> length ead1
          in 
  (FBytes.repr_bytes (method_as_nat msg1.method))
    + (FBytes.repr_bytes msg1.suite_i)
    + (length msg1.g_x)
    + (length msg1.c_i)
    + ead_len

val concat_msg1:
  #cs:supported_cipherSuite
  -> msg1:message1 #cs
  -> Tot (lbytes (concat_msg1_get_length msg1))

val lemma_concat_msg1_equiv:
  #cs:supported_cipherSuite
  -> msg1:message1 #cs
  -> Lemma (ensures (
    let msg1_concat = concat_msg1 #cs msg1 in
    let msg1_concat:lbytes (length msg1_concat) = msg1_concat in
    let g_x_len = length msg1.g_x in
    let c_i_len = length msg1.c_i in

    Seq.equal (nat_to_bytes (method_as_nat msg1.method)) (sub msg1_concat 0 1)
    /\ Seq.equal (nat_to_bytes msg1.suite_i ) (sub msg1_concat 1 1)
    /\ Seq.equal msg1.g_x (sub msg1_concat 2 g_x_len)
    /\ Seq.equal msg1.c_i (sub msg1_concat (2 + g_x_len) c_i_len)
    /\ (Some? msg1.ead1 ==> (
      let ead1 = Some?.v msg1.ead1 in
      let ead1_len = length ead1 in
      let ead1:lbytes ead1_len = ead1 in
      Seq.equal ead1 (sub msg1_concat (2 + g_x_len + c_i_len) ead1_len)
    ))
  ))
  [SMTPat (concat_msg1 #cs msg1)]

/// ------------------------
/// Plaintext 2
/// ------------------------

let construct_ptx2 #cs #auth_material (c_r:c_id_bytes) (id_cred_r:id_cred_i_bytes)
  (sig_or_mac2:sig_or_mac23_bytes cs auth_material) (ead2:option ead_bytes)
  :plaintext2 #cs #auth_material
  = {
    c_r = c_r;
    id_cred_r = id_cred_r;
    sig_or_mac2 = sig_or_mac2;
    ead2 = ead2;
  }

inline_for_extraction
let concat_ptx2_get_length (#cs:supported_cipherSuite)
  (#auth_material:authentication_material) (ptx2:plaintext2 #cs #auth_material)
  = let ead_len = match ptx2.ead2 with
          | None -> 0
          | Some ead2 -> length ead2
          in
    (length ptx2.c_r) + (length ptx2.id_cred_r)
    + (length ptx2.sig_or_mac2) + ead_len

let concat_ptx2 (#cs:supported_cipherSuite)
  (#auth_material:authentication_material) (ptx2:plaintext2 #cs #auth_material)
  : Tot (lbytes (concat_ptx2_get_length ptx2))
  = let c_r_lbyte:lbytes (length ptx2.c_r) = ptx2.c_r in
  let id_cred_r_lbyte:lbytes (length ptx2.id_cred_r) = ptx2.id_cred_r in
  let sig_or_mac2_lbyte:lbytes (sig_or_mac23_size cs auth_material)
    = ptx2.sig_or_mac2 in
  let temp = c_r_lbyte @< id_cred_r_lbyte @< sig_or_mac2_lbyte in
  match ptx2.ead2 with
    | None -> (
      temp
    )
    | Some ead2 -> (
      let ead2:lbytes (length ead2) = ead2 in
      temp @< ead2
    )

// val concat_ptx2:
//   #cs:supported_cipherSuite
//   -> #auth_material:authentication_material
//   -> ptx2:plaintext2 #cs #auth_material
//   -> Tot (lbytes (concat_ptx2_get_length ptx2))

inline_for_extraction
val serialize_ptx2_get_length:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx2:plaintext2 #cs #auth_material
  -> Tot (ptxt2_ctxt2_size cs auth_material)

val serialize_ptx2:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx2:plaintext2 #cs #auth_material
  -> Tot (lbytes (serialize_ptx2_get_length ptx2))

val deserialize_ptx2_raw_bytes:
  cs:supported_cipherSuite
  -> auth_material:authentication_material
  -> serialized_ptx2:plaintext2_bytes cs auth_material
  -> Tot (c_id_bytes & id_cred_i_bytes & sig_or_mac23_bytes cs auth_material
    & option ead_bytes)

/// Lemmas for ptx2

val lemma_deserialize_ptx2_raw_bytes:
  cs:supported_cipherSuite
  -> auth_material:authentication_material
  -> serialized_ptx2:plaintext2_bytes cs auth_material
  -> Lemma (ensures (
    let ptx2:lbytes (length serialized_ptx2) = serialized_ptx2 in
    let (c_id, id_cred, sig_or_mac2, ead2_op)
      = deserialize_ptx2_raw_bytes cs auth_material serialized_ptx2 in
    let sig_or_mac2_len = sig_or_mac23_size cs auth_material in
    let ptx2_min_len = c_id_size + id_cred_size + sig_or_mac2_len in

    Seq.equal c_id (Seq.sub ptx2 0 c_id_size)
    /\ Seq.equal id_cred (Seq.sub ptx2 c_id_size id_cred_size)
    /\ Seq.equal sig_or_mac2 (Seq.sub ptx2 (c_id_size + id_cred_size) sig_or_mac2_len)
    /\ (length serialized_ptx2 > ptx2_min_len <==> Some? ead2_op)
    /\ (length serialized_ptx2 > ptx2_min_len ==> (
      let ead2 = Some?.v ead2_op in
      let ead2_len = length ead2 in
      Seq.equal ead2 (Seq.sub ptx2 ptx2_min_len ead2_len)
    ))
  ))
  [SMTPat (deserialize_ptx2_raw_bytes cs auth_material serialized_ptx2)]

val lemma_concat_ptx2_equiv:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx2:plaintext2 #cs #auth_material
  -> Lemma (ensures (
    let ptx2_concat = concat_ptx2 #cs #auth_material ptx2 in
    let ptx2_concat:lbytes (length ptx2_concat) = ptx2_concat in
    
    let c_r_len = length ptx2.c_r in
    let id_cred_r_len = length ptx2.id_cred_r in
    let sig_or_mac2_len = length ptx2.sig_or_mac2 in

    Seq.equal ptx2.c_r (Seq.sub ptx2_concat 0 c_r_len)
    /\ Seq.equal ptx2.id_cred_r (Seq.sub ptx2_concat c_r_len id_cred_r_len)
    /\ Seq.equal ptx2.sig_or_mac2 (Seq.sub ptx2_concat (c_r_len + id_cred_r_len) sig_or_mac2_len)
    /\ (Some? ptx2.ead2 ==> (
      let ead2 = Some?.v ptx2.ead2 in
      let ead2:lbytes (length ead2) = ead2 in
      Seq.equal ead2 (Seq.sub ptx2_concat (c_r_len + id_cred_r_len + sig_or_mac2_len) (length ead2))
    ))
  ))
  [SMTPat (concat_ptx2 #cs #auth_material ptx2)]

val lemma_concat_serialize_ptx2_equiv:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx2:plaintext2 #cs #auth_material
  -> Lemma (ensures (
    let serialized_ptx2 = serialize_ptx2 #cs #auth_material ptx2 in
    concat_ptx2 #cs #auth_material ptx2 == serialized_ptx2
  ))
  [SMTPat (serialize_ptx2 #cs #auth_material ptx2)]

val lemma_deserialize_serialize_equiv:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx2:plaintext2 #cs #auth_material
  -> Lemma (ensures (
    let serialized_ptx2 = serialize_ptx2 #cs #auth_material ptx2 in
    let (c_r, id_cred_r, sig_or_mac2, ead2)
      = deserialize_ptx2_raw_bytes cs auth_material serialized_ptx2 in

    Seq.equal c_r ptx2.c_r
    /\ Seq.equal id_cred_r ptx2.id_cred_r
    /\ Seq.equal sig_or_mac2 ptx2.sig_or_mac2
    /// Currently, this model does not support variant-length EAD
    // /\ (Some? ead2 <==> Some? ptx2.ead2)
    /\ (Some? ptx2.ead2 /\ (length (Some?.v ptx2.ead2) > 0) ==> (
      let de_ead2 = Some?.v ead2 in
      let se_ead2 = Some?.v ptx2.ead2 in

      let de_ead2:lbytes (length de_ead2) = de_ead2 in
      let se_ead2:lbytes (length se_ead2) = se_ead2 in

      Seq.equal se_ead2 de_ead2
    ))
  ))
  [SMTPat (serialize_ptx2 #cs #auth_material ptx2)]

val lemma_deserialize_ptx2_raw_bytes_if_ead2:
  cs:supported_cipherSuite
  -> auth_material:authentication_material
  -> serialized_ptx2:plaintext2_bytes cs auth_material
  -> Lemma (ensures 
    (
      let (c_id, id_cred, sig_or_mac2, ead2) = deserialize_ptx2_raw_bytes cs auth_material serialized_ptx2 in
      (length serialized_ptx2 > min_ptx2_size cs auth_material) <==> Some? ead2
    )
  )
  [SMTPat (deserialize_ptx2_raw_bytes cs auth_material serialized_ptx2)]

/// ------------------------
/// Message 2
/// ------------------------

let construct_msg2 #cs #auth (g_y:ec_pub_key cs)
  (ciphertext2:ciphertext2_bytes cs auth)
  :message2 #cs #auth
  = {
    g_y = g_y;
    ciphertext2 = ciphertext2;
  }

let concat_msg2_get_length (#cs:supported_cipherSuite)
  (#auth_material:authentication_material) (msg2:message2 #cs #auth_material)
  = (length msg2.g_y) + (length msg2.ciphertext2)

let concat_msg2 (#cs:supported_cipherSuite)
  (#auth_material:authentication_material) (msg2:message2 #cs #auth_material)
  = let g_y_lbytes:lbytes (length msg2.g_y) = msg2.g_y in
  let ciphertext2_lbytes:lbytes (length msg2.ciphertext2) = msg2.ciphertext2 in
  g_y_lbytes @< ciphertext2_lbytes

let serialize_msg2_get_length (#cs:supported_cipherSuite)
  (#auth_material:authentication_material) (msg2:message2 #cs #auth_material)
  = concat_msg2_get_length msg2

let serialize_msg2 (#cs:supported_cipherSuite)
  (#auth_material:authentication_material) (msg2:message2 #cs #auth_material)
  = concat_msg2 #cs #auth_material msg2
  // let serialized_g_y = serialize_lbytes msg2.g_y in
  // let serialized_ciphertext2 = serialize_bytes msg2.ciphertext2 in
  // serialized_g_y @< serialized_ciphertext2

/// Lemmas for Message 2
let lemma_serialize_msg2_get_length_concat_equiv
  (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (msg2:message2 #cs #auth_material)
  : Lemma (ensures (
    serialize_msg2_get_length msg2 = concat_msg2_get_length msg2
  ))
  [SMTPat (serialize_msg2_get_length #cs #auth_material msg2)]
  = ()

let lemma_concat_serialize_msg2_equiv
  (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (msg2:message2 #cs #auth_material)
  : Lemma (ensures (
    let serialized_msg2 = serialize_msg2 msg2 in
    concat_msg2 msg2 == serialized_msg2
  ))
  [SMTPat (serialize_msg2 #cs #auth_material msg2)]
  = ()

/// ------------------------
/// Plaintext 3
/// ------------------------

let construct_ptx3 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
    (id_cred_i:id_cred_i_bytes) (sig_or_mac3:sig_or_mac23_bytes cs auth_material)
    (ead3:option ead_bytes)
    :plaintext3 #cs #auth_material
    = {
      id_cred_i = id_cred_i;
      sig_or_mac3 = sig_or_mac3;
      ead3 = ead3;
    }


// val concat_ptx3_get_length:
//   #cs:supported_cipherSuite
//   -> #auth_material:authentication_material
//   -> ptx3:plaintext3 #cs #auth_material
//   -> Tot (plaintext3_size cs auth_material)

let concat_ptx3_get_length
  (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx3:plaintext3 #cs #auth_material)
  = let ead_len = match ptx3.ead3 with
                  | None -> 0
                  | Some ead3 -> length ead3
                  in
  assert(ead_len = 0);
  let temp = (length ptx3.id_cred_i) + (length ptx3.sig_or_mac3)
        + ead_len in
  assert(is_valid_ptx3_size cs auth_material temp);
  assert(temp = (length ptx3.id_cred_i) + (length ptx3.sig_or_mac3));
  temp

val concat_ptx3:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx3:plaintext3 #cs #auth_material
  -> Tot (lbytes (concat_ptx3_get_length ptx3))

val lemma_concat_ptx3_equiv:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx3:plaintext3 #cs #auth_material
  -> Lemma (ensures (
    let ptx3_concat = concat_ptx3 ptx3 in
    match ptx3.ead3 with
      | None -> equal ptx3_concat (ptx3.id_cred_i @< ptx3.sig_or_mac3)
      | Some ead3 -> (
        let ead3:lbytes (length ead3) = ead3 in
        equal ptx3_concat (ptx3.id_cred_i @< ptx3.sig_or_mac3 @< ead3)
      )
  ))
  [SMTPat (concat_ptx3 #cs #auth_material ptx3)]

val serialize_ptx3_get_length:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx3:plaintext3 #cs #auth_material
  -> Tot (plaintext3_size cs auth_material)

val lemma_serialize_ptx3_get_length_concat_equiv:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx3:plaintext3 #cs #auth_material
  -> Lemma (ensures (
    let ptx3_concat_len = concat_ptx3_get_length ptx3 in
    ptx3_concat_len = serialize_ptx3_get_length ptx3
    /\ ptx3_concat_len = length ptx3.id_cred_i + length ptx3.sig_or_mac3
  ))
  [SMTPat (concat_ptx3_get_length #cs #auth_material ptx3);
  SMTPat (serialize_ptx3_get_length #cs #auth_material ptx3)]

val serialize_ptx3:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx3:plaintext3 #cs #auth_material
  -> Tot (lbytes (serialize_ptx3_get_length ptx3))

val deserialize_ptx3_raw_bytes:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> serialized_ptx3:plaintext3_bytes cs auth_material
  -> Tot (id_cred_i_bytes & sig_or_mac23_bytes cs auth_material & option ead_bytes)

/// Lemmas for ptx3
val lemma_deserialize_ptx3_raw_bytes_if_ead3:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> serialized_ptx3:plaintext3_bytes cs auth_material
  -> Lemma
  (ensures (
    let (id_cred_i, sig_or_mac3, ead3) = deserialize_ptx3_raw_bytes #cs #auth_material serialized_ptx3 in
    length serialized_ptx3 > min_ptx3_size cs auth_material <==> Some? ead3
  ))
  [SMTPat (deserialize_ptx3_raw_bytes #cs #auth_material serialized_ptx3)]

val lemma_deserialize_ptx3:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> serialized_ptx3:plaintext3_bytes cs auth_material
  -> Lemma (ensures (
    let (id_cred_i, sig_or_mac3, ead3_op)
      = deserialize_ptx3_raw_bytes #cs #auth_material serialized_ptx3 in
    let serialized_ptx3:lbytes (length serialized_ptx3) = serialized_ptx3 in
    
    let sig_or_mac3_len = sig_or_mac23_size cs auth_material in
    assert(length sig_or_mac3 = sig_or_mac3_len);
    assert(length id_cred_i = id_cred_size);
    let ptx3_min_len = id_cred_size + sig_or_mac3_len in

    Seq.equal id_cred_i (Seq.sub serialized_ptx3 0 id_cred_size)
    /\ Seq.equal sig_or_mac3 (Seq.sub serialized_ptx3 id_cred_size sig_or_mac3_len)
    /\ (length serialized_ptx3 > ptx3_min_len <==> Some? ead3_op)
    /\ (length serialized_ptx3 > ptx3_min_len ==> (
      let ead3 = Some?.v ead3_op in
      let ead3_len = length ead3 in
      Seq.equal ead3 (Seq.sub serialized_ptx3 ptx3_min_len ead3_len)
    ))
  ))
  [SMTPat (deserialize_ptx3_raw_bytes #cs #auth_material serialized_ptx3)]

val lemma_serialize_then_deserialize_ptx3_equiv:
  #cs:supported_cipherSuite
  -> #auth_material: authentication_material
  -> ptx3:plaintext3 #cs #auth_material
  -> Lemma (ensures (
    let serialized_ptx3 = serialize_ptx3 ptx3 in
    let (id_cred_i, sig_or_mac3, ead3)
      = deserialize_ptx3_raw_bytes #cs #auth_material serialized_ptx3 in

    Seq.equal ptx3.id_cred_i id_cred_i
    /\ Seq.equal ptx3.sig_or_mac3 sig_or_mac3
    /\ ((Some? ptx3.ead3 /\ (length (Some?.v ptx3.ead3)) > 0) <==> Some? ead3)
    /\ (Some? ead3 ==> (
      let de_ead3 = Some?.v ead3 in
      let se_ead3 = Some?.v ptx3.ead3 in

      let de_ead3:lbytes (length de_ead3) = de_ead3 in
      let se_ead3:lbytes (length se_ead3) = se_ead3 in

      Seq.equal se_ead3 de_ead3
    ))
  ))
  [SMTPat (serialize_ptx3 #cs #auth_material ptx3)]

// val lemma_concat_serialize_ptx3_equiv:
//   #cs:supported_cipherSuite
//   -> #auth_material:authentication_material
//   -> ptx3:plaintext3 #cs #auth_material
//   -> Lemma (ensures (
//     serialize_ptx3 #cs #auth_material ptx3 == concat_ptx3 #cs #auth_material ptx3
//   ))
//   [SMTPat (serialize_ptx3 #cs #auth_material ptx3)]

/// ------------------------
/// Message 3
/// ------------------------

/// Message 3 is just a ciphertext of plaintext3
/// only a single field, no need to do serialization/deserialization