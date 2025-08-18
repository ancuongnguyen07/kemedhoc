module Spec.EDHOC.KeySchedule

module Seq = Lib.Sequence
module BSeq = Lib.ByteSequence

// module Def = Spec.EDHOC.Base.Definitions
// module FBytes = FStar.Bytes

#reset-options "--initial_fuel 2 --max_fuel 12 --initial_ifuel 2 --max_ifuel 8 --z3rlimit 15"

(*--------------------------- HKDF Info*)
let construct_info label context okm_len =
  {
    label = label;
    context = context;
    okm_len = okm_len
  }

// let concat_info_get_length i
//   = (FBytes.repr_bytes i.label)
//     + (length i.context)
//     + (FBytes.repr_bytes i.okm_len)

let concat_info i
  = let label_bytes = nat_to_bytes i.label in
  let context_length = length i.context in
  let context_lbytes: lbytes context_length = i.context in
  let okm_len_bytes = nat_to_bytes i.okm_len in
  label_bytes @< context_lbytes @< okm_len_bytes

let construct_info_to_bytes label context okm_len
  = let info = construct_info label context okm_len in
  concat_info info

let lemma_construct_info_to_bytes_equiv_concat label context okm_len
  = ()


let serialize_info_get_length (i:info)
  = (FBytes.repr_bytes i.label) + offset
    + (length i.context) + offset
    + (FBytes.repr_bytes i.okm_len) + offset

let serialize_info (i:info)
  = let label_bytes = serialize_nat_to_bytes i.label in
  let okm_len_bytes = serialize_nat_to_bytes i.okm_len in
  let context_bytes = serialize_bytes i.context in
  label_bytes @< context_bytes @< okm_len_bytes

(*--------------------------- Context2*)
let construct_context2 c_r id_cred_r th2 cred_r ead2 =
  {
    c_r = c_r;
    id_cred_r = id_cred_r;
    th2 = th2;
    cred_r = cred_r;
    ead2 = ead2;
  }


let concat_context2 #cs ctx2
  = let c_r_lbytes: lbytes (length ctx2.c_r) = ctx2.c_r in
  let id_cred_r_lbytes: lbytes (length ctx2.id_cred_r) = ctx2.id_cred_r in
  let cred_r_lbytes: lbytes (length ctx2.cred_r) = ctx2.cred_r in
  let ead2_lbytes = match ctx2.ead2 with
      | None -> lbytes_empty
      | Some v -> v
      in
  c_r_lbytes @< id_cred_r_lbytes @< ctx2.th2 @< cred_r_lbytes @< ead2_lbytes

let construct_context2_to_bytes #cs c_r id_cred_r th2 cred_r ead2
  = let ctx2 = construct_context2 c_r id_cred_r th2 cred_r ead2 in
  concat_context2 ctx2

let lemma_construct_context2_to_bytes_equiv_concat #cs c_r id_cred_r th2 cred_r ead2
  = ()


let serialize_context2_get_length #cs ctx2
  = let ead2_length_offset = match ctx2.ead2 with
                  | None -> 0
                  | Some b -> (length b) + offset
                  in 
  (length ctx2.c_r) + offset
    + (length ctx2.id_cred_r) + offset
    + (hash_size cs) + offset
    + (length ctx2.cred_r) + offset
    + ead2_length_offset

let serialize_context2 ctx2
  = let c_r_bytes = serialize_bytes ctx2.c_r in
  let id_cred_r_bytes = serialize_bytes ctx2.id_cred_r in
  let th2_bytes = serialize_bytes ctx2.th2 in
  let cred_r_bytes = serialize_bytes ctx2.cred_r in
  let temp = c_r_bytes @< id_cred_r_bytes @< th2_bytes @< cred_r_bytes in
  match ctx2.ead2 with
      | None -> temp
      | Some b -> temp @< (serialize_bytes b)

(*--------------------------- Context3*)
let construct_context3 id_cred_i th3 cred_i ead3 =
  {
    id_cred_i = id_cred_i;
    th3 = th3;
    cred_i = cred_i;
    ead3 = ead3;
  }


let concat_context3 #cs ctx3
  = let id_cred_i_lbytes:lbytes (length ctx3.id_cred_i) = ctx3.id_cred_i in
  let cred_i_lbytes:lbytes (length ctx3.cred_i) = ctx3.cred_i in
  let ead3_lbytes = match ctx3.ead3 with
      | None -> lbytes_empty
      | Some v -> v
      in
  id_cred_i_lbytes @< ctx3.th3 @< cred_i_lbytes @< ead3_lbytes

let construct_context3_to_bytes #cs id_cred_i th3 cred_i ead3
  = let ctx3 = construct_context3 id_cred_i th3 cred_i ead3 in
  concat_context3 ctx3

let lemma_construct_context3_to_bytes_equiv_concat #cs id_cred_i th3 cred_i ead3
  = ()

let serialize_context3_get_length #cs ctx3
  = let ead3_length_offset = match ctx3.ead3 with
                | None -> 0
                | Some b -> (length b) + offset
                in
    (length ctx3.id_cred_i) + offset
    + (hash_size cs) +  offset
    + (length ctx3.cred_i) + offset
    + ead3_length_offset

let serialize_context3 (ctx3:context3)
  = let id_cred_i_bytes = serialize_bytes ctx3.id_cred_i in
  let th3_bytes = serialize_bytes ctx3.th3 in
  let cred_i_bytes = serialize_bytes ctx3.cred_i in
  let temp = id_cred_i_bytes @< th3_bytes @< cred_i_bytes in
  match ctx3.ead3 with
      | None -> temp
      | Some b -> temp @< (serialize_bytes b)
  
(*--------------------- PRK*)
/// all PRKs are the output of HMAC_extract

/// TH2 is Salt
/// G_XY is IKM
/// PRK2e = HKDF_Extract(TH2, G_XY)
let extract_prk2e #cs th2 g_xy
  = hkdf_extract cs th2 g_xy

/// PRK3e2m = HKDF_Extract(SALT3e2m, G_RX)
/// OR PRK3e2m = PRK2e if signature-based authentication is used.
let extract_prk3e2m #cs salt3e2m g_rx
  = hkdf_extract cs salt3e2m g_rx

let lemma_extract_prk3e2m_equality #cs salt1 salt2 ikm1 ikm2
  = ()

/// PRK4e3m = HKDF_Extract(SALT4e3m, G_IY)
/// OR PRK4e3m = PRK3e2m if signature-based authentication is used.
let extract_prk4e3m #cs salt4e3m g_iy
  = hkdf_extract cs salt4e3m g_iy

/// PRK_OUT = HKDF_Expand(PRK4e3m, 7, TH_4, hash_length)
///         = EDHOC_KDF(PRK4e3m, info, hash_length)
/// where info = {
///         label: 7,
///         context: TH_4,
///         okm_len: hash_length   
/// }
let expand_prk_out #cs prk4e3m th4
  = let info_bytes = construct_info_to_bytes info_label_prk_out th4 (hash_size cs) in
  hkdf_expand cs prk4e3m info_bytes (hash_size cs)

/// PRK_Exporter  = HKDF_Expand(PRK_OUT, 10, empty_byte, hash_length)
///               = EDHOC_KDF(PRK_OUT, info, hash_length)
/// where info = {
///         label: 10,
///         context: empty_byte,
///         okm_len: hash_length   
/// }
let expand_prk_exporter #cs prk_out
  = let info_label_bytes = nat_to_bytes info_label_prk_exporter in
  let okm_len_bytes = nat_to_bytes (hash_size cs) in
  let info_bytes = info_label_bytes @< okm_len_bytes in
  // let info_bytes = construct_info_to_bytes info_label_prk_exporter bytes_empty (hash_size cs) in
  hkdf_expand cs prk_out info_bytes (hash_size cs)

(*---------------------- Encryption Key*)
/// KEYSTREAM2  = HKDF_Expand(PRK2e, 0, TH_2, plaintext2_length)
///             = EDHOC_KDF(PRK2e, info, plaintext2_length)
/// where info = {
///         label: 0,
///         context: TH_2,
///         okm_len: plaintext2_length   
/// }
let expand_keystream2 #cs prk2e th2 ptx2_len
  = let info_bytes = construct_info_to_bytes info_label_keystream2 th2 ptx2_len in
  hkdf_expand cs prk2e info_bytes ptx2_len

/// K3  = HKDF_Expand(PRK3e2m, 3, TH_3, key_length)
///     = EDHOC_KDF(PRK3e2m, info, key_length)
/// where info = {
///         label: 3,
///         context: TH_3,
///         okm_len: key_length
/// }
let expand_k3 #cs prk3e2m th3
  = let aead_alg = get_aead_alg cs in 
  let info_bytes = construct_info_to_bytes info_label_k3 th3 (aead_key_size aead_alg) in
  hkdf_expand cs prk3e2m info_bytes (aead_key_size aead_alg)

(*---------------------- Initial Vector*)
/// IV_3  = HKDF_Expand(PRK3e2m, 4, TH_3, iv_length)
///       = EDHOC_KDF(PRK3e2m, info, iv_length)
/// where info = {
///         label: 4,
///         context: TH_3,
///         okm_len: iv_length
/// }
let expand_iv3 #cs prk3e2m th3
  = let info_bytes = construct_info_to_bytes info_label_iv3 th3 aead_iv_size in
  hkdf_expand cs prk3e2m info_bytes aead_iv_size

(*---------------------- SALT*)
/// SALT3e2m  = HKDF_Expand(PRK2e, 1, TH_2, hash_length)
///           = EDHOC_KDF(PRK2e, info, hash_length)
/// where info = {
///         label: 1,
///         context: TH_2,
///         okm_len: hash_length
/// }
let expand_salt3e2m #cs prk2e th2
  = let info_bytes = construct_info_to_bytes info_label_salt3e2m th2 (hash_size cs) in
  hkdf_expand cs prk2e info_bytes (hash_size cs)

/// SALT4e3m  = HKDF_Expand(PRK3e2m, 5, TH_3, hash_length)
///           = EDHOC_KDF(PRK3e2m, info, hash_length)
/// where info = {
///         label: 5,
///         context: TH_3,
///         okm_len: hash_length
/// }
let expand_salt4e3m #cs prk3e2m th3
  = let info_bytes = construct_info_to_bytes info_label_salt4e3m th3 (hash_size cs) in
  hkdf_expand cs prk3e2m info_bytes (hash_size cs)

(*---------------------- MAC*)
/// MAC_2   = HKDF_Expand(PRK3e2m, 2, context_2, mac2_length)
///         = EDHOC_KDF(PRK3e2m, info, mac2_length)
/// where info = {
///         label: 2,
///         context: context_2,
///         okm_len: mac2_length
/// }
/// If signatured-based authentication then mac2_length = hash_length
/// else mac2_length = mac_length depending on cipher suite.
let expand_mac2 #cs auth_mode prk3e2m ctx2
  = let ctx2_bytes = concat_context2 ctx2 in
  let mac2_length = mac23_size cs auth_mode in
  let info_bytes = construct_info_to_bytes info_label_mac2 ctx2_bytes mac2_length in
  hkdf_expand cs prk3e2m info_bytes mac2_length

/// MAC_3 = HKDF_Expand(PRK4e3m, 6, context_3, mac3_length)
///       = EDHOC_KDF(PRK4e3m, info, mac3_length)
/// where info = {
///         label: 6,
///         context: context_3
///         okm_len: mac3_length
/// }
/// If signatured-based authentication then mac3_length = hash_length
/// else mac3_length = mac_length depending on cipher suite.
let expand_mac3 #cs auth_mode prk4e3m ctx3
  = let ctx3_bytes = concat_context3 ctx3 in
  let mac3_length = mac23_size cs auth_mode in
  let info_bytes = construct_info_to_bytes info_label_mac3 ctx3_bytes mac3_length in
  hkdf_expand cs prk4e3m info_bytes mac3_length