module Spec.EDHOC.Parser

module FBytes = FStar.Bytes

// open FStar.Pervasives
// open FStar.Mul

(*HACL libs*)
// open Lib.IntTypes
// open Lib.RawIntTypes
// open Lib.ByteSequence
// open Lib.Sequence

// open Spec.EDHOC.Base.Definitions
// open Spec.EDHOC.CryptoPrimitives
// open Spec.EDHOC.Serialization
// open Spec.EDHOC.CommonPred

#set-options "--max_fuel 12 --max_ifuel 6 --z3rlimit 50"

let to_lbytes (#len:size_nat) (s:seq (uint_t U8 SEC))
  :option (lbytes len)
  = if length s = len then Some s else None

/// Sig_or_MAC23 utilities
// let sig_or_mac23_get_length #cs #auth_material sig_or_mac
//   = match sig_or_mac with
//     | Inl signature -> length signature
//     | Inr mac -> mac_size (get_aead_alg cs)
let sig_or_mac23_get_length sig_or_mac = length sig_or_mac

// let sig_or_mac23_get_bytes #cs #auth_material sig_or_mac
//   = match sig_or_mac with
//     | Inl signature -> signature
//     | Inr mac -> mac

// let is_valid_sig_or_mac23_length cs auth_material n
//   = match auth_material with
//     | Signature -> n = signature_size
//     | MAC -> n = mac_size (get_aead_alg cs)


// let bytes_to_sig_or_mac23_bytes cs auth_material raw_bytes
//   = let len_b = length raw_bytes in
//   if (is_valid_sig_or_mac23_length cs auth_material len_b)
//   then (
//     Some (
//       match auth_material with
//         | Signature -> Inl raw_bytes
//         | MAC -> (
//           assert (len_b = mac_size (get_aead_alg cs));
//           let lb:lbytes len_b = raw_bytes in
//           let cast_mac23:mac23 cs auth_material = lb in
//           Inr cast_mac23
//         )      
//       )
//   )
//   else None

/// Sig_or_MAC23 lemmas
// let lemma_sig_or_mac23_valid_length #cs #auth_material sig_or_mac = ()

(*--------------------------------------*)
(*---------------------------- Parsing*)
(*--------------------------------------*)

/// Message 1
let concat_msg1_get_length msg1
  = let ead_len = match msg1.ead1 with
          | None -> 0
          | Some ead1 -> length ead1
          in 
  (FBytes.repr_bytes (method_as_nat msg1.method))
    + (FBytes.repr_bytes msg1.suite_i)
    + (length msg1.g_x)
    + (length msg1.c_i)
    + ead_len

// let concat_msg1 #cs msg1
//   = let method_lbyte:lbytes 1 = nat_to_bytes (method_as_nat msg1.method) in
//   let suite_i_lbyte:lbytes 1 = nat_to_bytes msg1.suite_i in
//   let g_x_lbytes:lbytes (length msg1.g_x) = msg1.g_x in
//   let c_i_lbytes:lbytes (length msg1.c_i) = msg1.c_i in
//   let temp = method_lbyte @< suite_i_lbyte @< g_x_lbytes @< c_i_lbytes in
//   match msg1.ead1 with
//           | None -> temp
//           | Some ead1 -> (
//             let ead1:lbytes (length ead1) = ead1 in
//             temp @< ead1
//           )

/// Plaintext 2
inline_for_extraction
let concat_ptx2_get_length ptx2
  = let ead_len = match ptx2.ead2 with
          | None -> 0
          | Some ead2 -> length ead2
          in
    (length ptx2.c_r) + (length ptx2.id_cred_r)
    + (length ptx2.sig_or_mac2) + ead_len


inline_for_extraction
let serialize_ptx2_get_length ptx2
  = concat_ptx2_get_length ptx2
  
let serialize_ptx2 #cs #auth_material ptx2
  = concat_ptx2 #cs #auth_material ptx2
  // let serialized_c_r = serialize_bytes ptx2.c_r in
  // let serialized_id_cred_r = serialize_bytes ptx2.id_cred_r in
  // let sig_or_mac2_length = sig_or_mac23_get_length #cs ptx2.sig_or_mac2 in
  // let sig_or_mac2_op = to_lbytes #sig_or_mac2_length (sig_or_mac23_get_bytes #cs ptx2.sig_or_mac2) in
  // match sig_or_mac2_op with
  //   | None -> Fail SerializationDeserializationFailed
  //   | Some sig_or_mac2_lbytes -> (
  //     let serialized_sig_or_mac2 = serialize_lbytes sig_or_mac2_lbytes in
  //     let temp = serialized_c_r @< serialized_id_cred_r @< serialized_sig_or_mac2 in
  //     match ptx2.ead2 with
  //       | None -> Res temp
  //       | Some ead2 -> (
  //         let serialized_ead2 = serialize_bytes ead2 in
  //         Res (temp @< serialized_ead2)
  //       )
  //   )

// let check_deserialized_ptx2 (cs:supported_cipherSuite) (c_r:bytes) (id_cred_r:bytes)
//   (sig_or_mac2:bytes) (ead2:option ead_bytes)
//   :bool
//   = let sig_or_mac_len = length sig_or_mac2 in
//   if (
//     length c_r > c_id_max_size || length id_cred_r > id_cred_max_size
//     || (sig_or_mac_len <> (hash_size cs)
//         && sig_or_mac_len <> (mac_size (get_aead_alg cs))
//         && sig_or_mac_len <> signature_size
//       )
//   ) then false
//   else true

#push-options "--z3rlimit 50"
let deserialize_ptx2_raw_bytes cs auth_material serialized_ptx2
  = let total_size = length serialized_ptx2 in
  let ptx2_lbytes:lbytes total_size = serialized_ptx2 in

  let c_id:c_id_bytes = sub ptx2_lbytes 0 c_id_size in
  let id_cred:id_cred_i_bytes = sub ptx2_lbytes c_id_size id_cred_size in

  let sig_or_mac2:sig_or_mac23_bytes cs auth_material
    = sub ptx2_lbytes (c_id_size + id_cred_size) (sig_or_mac23_size cs auth_material) in
  let sig_or_mac2_len = length sig_or_mac2 in
  
  let min_size = min_ptx2_size cs auth_material in
  if total_size = min_size
  then (c_id, id_cred, sig_or_mac2, None)
  else (
    assert(total_size > min_size);
    /// NOTE! variant-length EAD is not supported now
    /// the below is just place holder for further proofs
    let ead2 = sub ptx2_lbytes (c_id_size + id_cred_size + sig_or_mac2_len) ead_max_size in
    (c_id, id_cred, sig_or_mac2, Some ead2)
  )
  // if (length serialized_ptx2 <= offset) then Fail SerializationDeserializationFailed
  // else (ead2_len
  //   let ret = deserialize_bytes serialized_ptx2 c_id_max_size 0 in
  //   let serialized_ptx2_len = length serialized_ptx2 in
  //   match ret with
  //     | Fail e -> Fail e
  //     | Res (c_r, cursor) -> (
  //       if (cursor + offset >= serialized_ptx2_len) then Fail SerializationDeserializationFailed
  //       else (
  //         let ret = deserialize_bytes serialized_ptx2 id_cred_max_size cursor in
  //         match ret with
  //           | Fail e -> Fail e
  //           | Res (id_cred_r, cursor) -> (
  //             if (cursor + offset >= serialized_ptx2_len) then Fail SerializationDeserializationFailed
  //             else (
  //               let ret = deserialize_bytes serialized_ptx2 sig_or_mac_max_size cursor in
  //               match ret with
  //                 | Fail e -> Fail e
  //                 | Res (sig_or_mac2, cursor) -> (
  //                   // NOTE! Currently this implementation does not support EAD
  //                   let ead2 = None in
  //                   if (check_deserialized_ptx2 cs c_r id_cred_r sig_or_mac2 ead2)
  //                   then Res (c_r, id_cred_r, sig_or_mac2, ead2)
  //                   else Fail SerializationDeserializationFailed
  //                 )
  //             )
              
  //           )
  //       )
        
  //     )
  // )

  
#pop-options

/// Message 2
/// NO need to use the following functions as this high-level model
/// does not take care of CBOR serialization/deserialization


/// Plaintext 3
let concat_ptx3_get_length #cs #auth_material ptx3
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

let concat_ptx3 #cs #auth_material ptx3
  =
  // let id_cred_i_lbytes:lbytes (length ptx3.id_cred_i) = ptx3.id_cred_i in
  // let sig_or_mac3_length = sig_or_mac23_get_length #cs ptx3.sig_or_mac3 in
  // let sig_or_mac3_op = to_lbytes #sig_or_mac3_length (sig_or_mac23_get_bytes #cs ptx3.sig_or_mac3) in
  // match sig_or_mac3_op with
  //   | None -> Fail SerializationDeserializationFailed
  //   | Some sig_or_mac3_lbytes -> (
  //       let temp = id_cred_i_lbytes @< sig_or_mac3_lbytes in
  //       Res (match ptx3.ead3 with
  //               | None -> temp
  //               | Some ead3 -> temp @< ead3)
  //   )
  let temp = ptx3.id_cred_i @< ptx3.sig_or_mac3 in
  match ptx3.ead3 with
    | None -> temp
    | Some ead3 -> (
      let ead3:lbytes (length ead3) = ead3 in
      temp @< ead3
    )


let serialize_ptx3_get_length ptx3
  = concat_ptx3_get_length ptx3


let serialize_ptx3 #cs #auth_material ptx3
  = concat_ptx3 ptx3
  // let serialized_id_cred_i = serialize_bytes ptx3.id_cred_i in
  // let sig_or_mac3_length = sig_or_mac23_get_length #cs ptx3.sig_or_mac3 in
  // let sig_or_mac3_op = to_lbytes #sig_or_mac3_length (sig_or_mac23_get_bytes #cs ptx3.sig_or_mac3) in
  // match sig_or_mac3_op with
  //   | None -> Fail SerializationDeserializationFailed
  //   | Some sig_or_mac3_lbytes -> (
  //     let serialized_sig_or_mac3 = serialize_lbytes sig_or_mac3_lbytes in
  //     let temp = serialized_id_cred_i @< serialized_sig_or_mac3 in
  //     match ptx3.ead3 with
  //       | None -> Res temp
  //       | Some ead3 -> (
  //         let serialized_ead3 = serialize_bytes ead3 in
  //         Res (temp @< serialized_ead3)
  //       )
  //   )

// let check_deserialized_ptx3 (cs:supported_cipherSuite) (id_cred_i:bytes)
//   (sig_or_mac3:bytes) (ead3:option ead_bytes)
//   :bool
//   = let sig_or_mac_len = length sig_or_mac3 in
//   if (
//     length id_cred_i > id_cred_max_size
//     || (sig_or_mac_len <> (hash_size cs)
//         && sig_or_mac_len <> (mac_size (get_aead_alg cs))
//         && sig_or_mac_len <> signature_size
//       )
//   ) then false
//   else true

let deserialize_ptx3_raw_bytes #cs #auth_material serialized_ptx3
  =
  // if (length serialized_ptx3 <= offset) then Fail SerializationDeserializationFailed
  // else (
  //   let res = deserialize_bytes serialized_ptx3 id_cred_max_size 0 in
  //   match res with
  //     | Fail e -> Fail e
  //     | Res (id_cred_i, cursor) -> (
  //       let serialized_ptx3_len = length serialized_ptx3 in
  //       if (cursor + offset >= serialized_ptx3_len) then Fail SerializationDeserializationFailed
  //       else (
  //         let res = deserialize_bytes serialized_ptx3 sig_or_mac_max_size cursor in
  //         match res with
  //           | Fail e -> Fail e
  //           | Res (sig_or_mac3_raw_bytes, cursor) -> (
  //             let ead3 = None in
  //             if (check_deserialized_ptx3 cs id_cred_i sig_or_mac3_raw_bytes ead3)
  //             then Res (id_cred_i, sig_or_mac3_raw_bytes, ead3)
  //             else Fail SerializationDeserializationFailed
  //           )
  //       )
        
  //     )
  // )
  let total_size = length serialized_ptx3 in
  let ptx3_lbytes:lbytes total_size = serialized_ptx3 in

  let id_cred_i:id_cred_i_bytes = sub ptx3_lbytes 0 id_cred_size in

  let sig_or_mac3:sig_or_mac23_bytes cs auth_material
    = sub ptx3_lbytes id_cred_size (sig_or_mac23_size cs auth_material) in
  let sig_or_mac3_len = length sig_or_mac3 in
  
  let min_size = min_ptx3_size cs auth_material in
  if (total_size = min_size)
  then (id_cred_i, sig_or_mac3, None)
  else (
    assert(total_size > min_size);
    /// NOTE! variant-length EAD is not supported now
    /// the below is just place holder for further proofs
    let ead3 = sub ptx3_lbytes (id_cred_size + sig_or_mac3_len) ead_max_size in
    (id_cred_i, sig_or_mac3, Some ead3)
  )

/// Message 3

