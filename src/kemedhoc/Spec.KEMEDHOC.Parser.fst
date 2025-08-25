module Spec.KEMEDHOC.Parser

// (*HACL libs*)
// open Lib.IntTypes
// // open Lib.RawIntTypes
// open Lib.ByteSequence
// open Lib.Sequence

module Seq = Lib.Sequence
module FBytes = FStar.Bytes

/// ------------------------
/// Plaintext 1
/// ------------------------
let concat_ptx1 ptx1
  = ptx1.id_cred_I @< ptx1.cred_I

let lemma_concat_ptx1_correctness ptx1
  = ()

let deserialize_ptx1 ptx1_byte
  = let id_cred_I = Seq.sub ptx1_byte 0 id_cred_size in
    let cred_I = Seq.sub ptx1_byte id_cred_size cred_size in
    { id_cred_I = id_cred_I; cred_I = cred_I }

let lemma_deserialize_ptx1_correctness ptx1
  = ()


/// ------------------------
/// Message 1
/// ------------------------

/// This implementation DOES NOT support EAD1
let concat_msg1 #kcs msg1
  = let method_byte = nat_to_bytes (method_enum_to_nat msg1.method) in
  let suite_i_byte = nat_to_bytes msg1.suite_i in
  method_byte @< suite_i_byte @< msg1.pk_x @< msg1.ct_auth_R @< msg1.c_i @< msg1.c1

let lemma_concat_msg1_correctness #kcs msg1
  = ()

/// ------------------------
/// Plaintext 2
/// ------------------------
let concat_ptx2 ptx2
  = ptx2.c_R @< ptx2.id_cred_R @< ptx2.cred_R @< ptx2.mac2

let lemma_concat_ptx2_correctness ptx2
  = ()

let deserialize_ptx2 #kcs ptx2_byte
  = let c_R = Seq.sub ptx2_byte 0 c_id_size in
    let id_cred_R = Seq.sub ptx2_byte c_id_size id_cred_size in
    let cred_R = Seq.sub ptx2_byte (c_id_size + id_cred_size) cred_size in
    let mac2 = Seq.sub ptx2_byte (c_id_size + id_cred_size + cred_size) (mac23_size kcs) in
    { c_R = c_R; id_cred_R = id_cred_R; cred_R = cred_R; mac2 = mac2 }

let lemma_deserialize_ptx2_correctness #kcs ptx2
  = ()

/// ------------------------
/// Message 2
/// ------------------------

let concat_msg2 #kcs msg2
  = msg2.ct_y @< msg2.ct_auth_I @< msg2.c2

let lemma_concat_msg2_correctness #kcs msg2
  = ()

/// ------------------------
/// Plaintext 3
/// ------------------------

let concat_ptx3 #kcs ptx3
  = ptx3.id_cred_I @< ptx3.mac3

let lemma_concat_ptx3_correctness #kcs ptx3
  = ()

let deserialize_ptx3 #kcs ptx3_byte
  = let id_cred_I = Seq.sub ptx3_byte 0 id_cred_size in
    let mac3 = Seq.sub ptx3_byte id_cred_size (mac23_size kcs) in
    { id_cred_I = id_cred_I; mac3 = mac3 }

let lemma_deserialize_ptx3_correctness #kcs ptx3
  = ()