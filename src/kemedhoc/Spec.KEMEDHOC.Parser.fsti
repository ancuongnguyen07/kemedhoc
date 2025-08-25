module Spec.KEMEDHOC.Parser

open FStar.Mul
open FStar.Pervasives

(*HACL libs*)
open Lib.IntTypes
// open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

module Seq = Lib.Sequence
module FBytes = FStar.Bytes

(*KEMEDHOC libs*)
open Spec.KEMEDHOC.CryptoPrimitives
open Spec.KEMEDHOC.Base.Definitions

(*EDHOC libs*)
open Spec.EDHOC.Serialization
module EdhocParser = Spec.EDHOC.Parser

/// constants for message fields
inline_for_extraction
let c_id_size = EdhocParser.c_id_size
inline_for_extraction
let id_cred_size = EdhocParser.id_cred_size
inline_for_extraction
let cred_size = EdhocParser.cred_size
inline_for_extraction
let okm_len_max_size = EdhocParser.okm_len_max_size

/// constant bytes for message fields
inline_for_extraction
type c_id_byte = lbytes c_id_size
inline_for_extraction
type id_cred_byte = lbytes id_cred_size
inline_for_extraction
type cred_byte = lbytes cred_size

///
/// NOTE!!! Currently this implementation does not support EAD
///
inline_for_extraction
let ead_max_size = 0

(*----- Plaintext sizes*)
inline_for_extraction
let plaintext1_size = id_cred_size + cred_size + ead_max_size
inline_for_extraction
let plaintext2_size (kcs: supportedKemCipherSuite)
  = c_id_size + id_cred_size + cred_size + ead_max_size + mac23_size kcs
inline_for_extraction
let plaintext3_size (kcs: supportedKemCipherSuite)
  = id_cred_size + ead_max_size + mac23_size kcs

(*------ Ciphertext sizes*)
inline_for_extraction
let c1_size (kcs: supportedKemCipherSuite)
  = plaintext1_size + aead_tag_size kcs
inline_for_extraction
let c2_size (kcs: supportedKemCipherSuite)
  = plaintext2_size kcs + aead_tag_size kcs
inline_for_extraction
let c3_size (kcs: supportedKemCipherSuite)
  = plaintext3_size kcs + aead_tag_size kcs


(*---------------------------- Plaintext 1*)
unopteq type plaintext1 = {
  id_cred_I: id_cred_byte;
  // does not support EAD1
  cred_I: cred_byte;
}

(*---------------------------- Message 1 Type*)
unopteq type message1 (#kcs: supportedKemCipherSuite) = {
  method: method_enum;
  suite_i: supportedKemCipherSuiteLabel;
  pk_x: kemPublicKey kcs;
  ct_auth_R: kemCiphertext kcs;
  c_i: c_id_byte;
  c1: lbytes (c1_size kcs);
  // does not support EAD1
}

let message1_equal (#kcs: supportedKemCipherSuite)
  (m1: message1 #kcs) (m2: message1 #kcs)
  : Type0
  = m1.method == m2.method
    /\ m1.suite_i = m2.suite_i
    /\ Seq.equal m1.pk_x m2.pk_x
    /\ Seq.equal m1.ct_auth_R m2.ct_auth_R
    /\ Seq.equal m1.c_i m2.c_i
    /\ Seq.equal m1.c1 m2.c1

(*---------------------------- Plaintext 2*)
unopteq type plaintext2 (#kcs: supportedKemCipherSuite) = {
  c_R: c_id_byte;
  id_cred_R: id_cred_byte;
  cred_R: cred_byte;
  // does not support EAD2
  mac2: mac23_byte kcs;
}

(*---------------------------- Message 2 Type*)
unopteq type message2 (#kcs: supportedKemCipherSuite) = {
  ct_y: kemCiphertext kcs;
  ct_auth_I: kemCiphertext kcs;
  c2: lbytes (c2_size kcs);
}

let message2_equal (#kcs: supportedKemCipherSuite)
  (m1: message2 #kcs) (m2: message2 #kcs)
  : Type0
  = Seq.equal m1.ct_y m2.ct_y
    /\ Seq.equal m1.ct_auth_I m2.ct_auth_I
    /\ Seq.equal m1.c2 m2.c2

(*---------------------------- Plaintext 3*)
unopteq type plaintext3 (#kcs: supportedKemCipherSuite) = {
  id_cred_I: id_cred_byte;
  // does not support EAD3
  mac3: mac23_byte kcs;
}

(*---------------------------- Message 3 Type*)
inline_for_extraction
type message3 (kcs: supportedKemCipherSuite) = lbytes (c3_size kcs)

(*--------------------------------------*)
(*---------------------------- Parsing*)
(*--------------------------------------*)

/// ------------------------
/// Plaintext 1
/// ------------------------

let construct_ptx1
  (id_cred_I: id_cred_byte)
  (cred_I: cred_byte)
  : plaintext1
  = {
    id_cred_I = id_cred_I;
    cred_I = cred_I;
  }

let concat_ptx1_get_length (ptx1: plaintext1)
  = Seq.length ptx1.id_cred_I
    + Seq.length ptx1.cred_I

val concat_ptx1:
  ptx1: plaintext1
  -> lbytes (concat_ptx1_get_length ptx1)

val lemma_concat_ptx1_correctness:
  ptx1: plaintext1
  -> Lemma (ensures (
    let concatenated_ptx1 = concat_ptx1 ptx1 in
    Seq.equal ptx1.id_cred_I (Seq.sub concatenated_ptx1 0 id_cred_size)
    /\ Seq.equal ptx1.cred_I (Seq.sub concatenated_ptx1 id_cred_size cred_size)
  ))
  [SMTPat (concat_ptx1 ptx1)]

val deserialize_ptx1:
  ptx1_byte: lbytes plaintext1_size
  -> plaintext1

val lemma_deserialize_ptx1_correctness:
  ptx1: plaintext1
  -> Lemma (ensures (
    let serialized_ptx1 = concat_ptx1 ptx1 in
    let deserialized_ptx1 = deserialize_ptx1 serialized_ptx1 in

    Seq.equal deserialized_ptx1.id_cred_I ptx1.id_cred_I
    /\ Seq.equal deserialized_ptx1.cred_I ptx1.cred_I
  ))
  [SMTPat (concat_ptx1 ptx1)]

/// ------------------------
/// Message 1
/// ------------------------

let concat_msg1_get_length (#kcs: supportedKemCipherSuite)
  (msg1: message1 #kcs)
  : size_nat
  = (FBytes.repr_bytes (method_enum_to_nat msg1.method))
  + (FBytes.repr_bytes msg1.suite_i)
  + (Seq.length msg1.pk_x)
  + (Seq.length msg1.ct_auth_R)
  + (Seq.length msg1.c_i)
  + (c1_size kcs)

/// Concatenate Message1 fields so that we can feed into
/// transcript hash 1
val concat_msg1:
  #kcs: supportedKemCipherSuite
  -> msg1:message1 #kcs
  -> lbytes (concat_msg1_get_length msg1)

val lemma_concat_msg1_correctness:
  #kcs: supportedKemCipherSuite
  -> msg1:message1 #kcs
  -> Lemma (ensures (
    let concatenated_msg1 = concat_msg1 msg1 in
    let pk_x_size = kem_public_key_size kcs in
    let ct_size = kem_ciphertext_size kcs in

    Seq.equal (nat_to_bytes (method_enum_to_nat msg1.method)) (Seq.sub concatenated_msg1 0 1)
    /\ Seq.equal (nat_to_bytes msg1.suite_i) (Seq.sub concatenated_msg1 1 1)
    /\ Seq.equal msg1.pk_x (Seq.sub concatenated_msg1 2 pk_x_size)
    /\ Seq.equal msg1.ct_auth_R (Seq.sub concatenated_msg1 (2 + pk_x_size) ct_size)
    /\ Seq.equal msg1.c_i (Seq.sub concatenated_msg1 (2 + pk_x_size + ct_size) c_id_size)
    /\ Seq.equal msg1.c1 (Seq.sub concatenated_msg1 (2 + pk_x_size + ct_size + c_id_size) (c1_size kcs))
  ))

/// ------------------------
/// Plaintext 2
/// ------------------------

let construct_ptx2 (#kcs: supportedKemCipherSuite)
  (c_R: c_id_byte) (id_cred_R: id_cred_byte)
  (cred_R: cred_byte) (mac2: mac23_byte kcs)
  : plaintext2 #kcs
  = {
    c_R = c_R;
    id_cred_R = id_cred_R;
    cred_R = cred_R;
    mac2 = mac2;
  }

let concat_ptx2_get_length (#kcs: supportedKemCipherSuite)
  (ptx2: plaintext2 #kcs)
  : size_nat
  = Seq.length ptx2.c_R
    + Seq.length ptx2.id_cred_R
    + Seq.length ptx2.cred_R
    + Seq.length ptx2.mac2

val concat_ptx2:
  #kcs: supportedKemCipherSuite
  -> ptx2: plaintext2 #kcs
  -> lbytes (concat_ptx2_get_length ptx2)

val lemma_concat_ptx2_correctness:
  #kcs: supportedKemCipherSuite
  -> ptx2: plaintext2 #kcs
  -> Lemma (ensures (
    let concatenated_ptx2 = concat_ptx2 ptx2 in

    Seq.equal ptx2.c_R (Seq.sub concatenated_ptx2 0 c_id_size)
    /\ Seq.equal ptx2.id_cred_R (Seq.sub concatenated_ptx2 c_id_size id_cred_size)
    /\ Seq.equal ptx2.cred_R (Seq.sub concatenated_ptx2 (c_id_size + id_cred_size) cred_size)
    /\ Seq.equal ptx2.mac2 (Seq.sub concatenated_ptx2 (c_id_size + id_cred_size + cred_size) (mac23_size kcs))
  ))

val deserialize_ptx2:
  #kcs: supportedKemCipherSuite
  -> ptx2_byte: lbytes (plaintext2_size kcs)
  -> plaintext2 #kcs

val lemma_deserialize_ptx2_correctness:
  #kcs: supportedKemCipherSuite
  -> ptx2: plaintext2 #kcs
  -> Lemma (ensures (
    let serialized_ptx2 = concat_ptx2 ptx2 in
    let deserialized_ptx2 = deserialize_ptx2 #kcs serialized_ptx2 in

    Seq.equal deserialized_ptx2.c_R ptx2.c_R
    /\ Seq.equal deserialized_ptx2.id_cred_R ptx2.id_cred_R
    /\ Seq.equal deserialized_ptx2.cred_R ptx2.cred_R
    /\ Seq.equal deserialized_ptx2.mac2 ptx2.mac2
  ))
  [SMTPat (concat_ptx2 #kcs ptx2)]

/// ------------------------
/// Message 2
/// ------------------------

let concstruct_msg2 (#kcs: supportedKemCipherSuite)
  (ct_y: kemCiphertext kcs)
  (ct_auth_I: kemCiphertext kcs)
  (c2: lbytes (c2_size kcs))
  : message2 #kcs
  = {
    ct_y = ct_y;
    ct_auth_I = ct_auth_I;
    c2 = c2;
  }

let concat_msg2_get_length (#kcs: supportedKemCipherSuite)
  (msg2: message2 #kcs)
  = Seq.length msg2.ct_y
    + Seq.length msg2.ct_auth_I
    + Seq.length msg2.c2

val concat_msg2:
  #kcs: supportedKemCipherSuite
  -> msg2: message2 #kcs
  -> lbytes (concat_msg2_get_length msg2)

val lemma_concat_msg2_correctness:
  #kcs: supportedKemCipherSuite
  -> msg2: message2 #kcs
  -> Lemma (ensures (
    let concatenated_msg2 = concat_msg2 msg2 in
    let ct_y_size = kem_ciphertext_size kcs in
    let ct_auth_I_size = kem_ciphertext_size kcs in

    Seq.equal msg2.ct_y (Seq.sub concatenated_msg2 0 ct_y_size)
    /\ Seq.equal msg2.ct_auth_I (Seq.sub concatenated_msg2 ct_y_size ct_auth_I_size)
    /\ Seq.equal msg2.c2 (Seq.sub concatenated_msg2 (ct_y_size + ct_auth_I_size) (c2_size kcs))
  ))
  [SMTPat (concat_msg2 #kcs msg2)]

/// ------------------------
/// Plaintext 3
/// ------------------------

let construct_ptx3 (#kcs: supportedKemCipherSuite)
  (id_cred_I: id_cred_byte)
  (mac3: mac23_byte kcs)
  : plaintext3 #kcs
  = {
    id_cred_I = id_cred_I;
    mac3 = mac3;
  }

let concat_ptx3_get_length (#kcs: supportedKemCipherSuite)
  (ptx3: plaintext3 #kcs)
  : size_nat
  = Seq.length ptx3.id_cred_I
    + Seq.length ptx3.mac3

val concat_ptx3:
  #kcs: supportedKemCipherSuite
  -> ptx3: plaintext3 #kcs
  -> lbytes (concat_ptx3_get_length ptx3)

val lemma_concat_ptx3_correctness:
  #kcs: supportedKemCipherSuite
  -> ptx3: plaintext3 #kcs
  -> Lemma (ensures (
    let concatenated_ptx3 = concat_ptx3 ptx3 in

    Seq.equal ptx3.id_cred_I (Seq.sub concatenated_ptx3 0 id_cred_size)
    /\ Seq.equal ptx3.mac3 (Seq.sub concatenated_ptx3 id_cred_size (mac23_size kcs))
  ))
  [SMTPat (concat_ptx3 #kcs ptx3)]

val deserialize_ptx3:
  #kcs: supportedKemCipherSuite
  -> ptx3_byte: lbytes (plaintext3_size kcs)
  -> plaintext3 #kcs

val lemma_deserialize_ptx3_correctness:
  #kcs: supportedKemCipherSuite
  -> ptx3: plaintext3 #kcs
  -> Lemma (ensures (
    let serialized_ptx3 = concat_ptx3 ptx3 in
    let deserialized_ptx3 = deserialize_ptx3 #kcs serialized_ptx3 in

    Seq.equal deserialized_ptx3.id_cred_I ptx3.id_cred_I
    /\ Seq.equal deserialized_ptx3.mac3 ptx3.mac3
  ))
  [SMTPat (concat_ptx3 #kcs ptx3)]
