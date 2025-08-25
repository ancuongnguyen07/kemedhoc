module Spec.KEMEDHOC.KeySchedule

module Seq = Lib.Sequence

(*---------------------------- HKDF Info*)
let construct_info label context okm_len
  : Tot info
  = {
      label = label;
      context = context;
      okm_len = okm_len;
    }

let concat_info i
  = let label_byte = nat_to_bytes i.label in
  let okm_len_byte = nat_to_bytes i.okm_len in
  let context_byte: lbytes (Seq.length i.context) = i.context in
  label_byte @< context_byte @< okm_len_byte

let lemma_concat_info_correctness i
  = ()

(*---------------------------- HKDF context*)

/// ---------------
/// Context 2
/// ---------------

let concat_context2 #kcs ctx2
  = ctx2.c_r @< ctx2.id_cred_r @< ctx2.th2 @< ctx2.cred_r

let lemma_concat_context2_correctness #kcs ctx2
  = ()

/// ---------------
/// Context 3
/// ---------------

let concat_context3 #kcs ctx3
  = ctx3.id_cred_i @< ctx3.th3 @< ctx3.cred_i

let lemma_concat_context3_correctness #kcs ctx3
  = ()

(*---------------------------- HKDF key schedule*)

/// ---------------
/// PRK
/// ---------------

let extract_prk1e #kcs th1 k_auth_R
  = hkdf_extract kcs th1 k_auth_R

let extract_prk2e #kcs prk1e th2 k_xy
  = let prk1e_th2_digest = do_hash kcs (prk1e @< th2) in
  hkdf_extract kcs prk1e_th2_digest k_xy

let extract_prk3e2m #kcs salt3e2m k_auth_R
  = hkdf_extract kcs salt3e2m k_auth_R

let extract_prk4e3m #kcs salt4e3m k_auth_I
  = hkdf_extract kcs salt4e3m k_auth_I

let expand_prk_out #kcs prk4e3m th4
  = let info_struct = construct_info info_label_prk_out th4 (hash_size kcs) in
  let info_byte = concat_info info_struct in

  hkdf_expand kcs prk4e3m info_byte (hash_size kcs)

let expand_prk_exporter #kcs prk_out
  = let info_label_byte = nat_to_bytes info_label_prk_exporter in
  let okm_len_byte = nat_to_bytes (hash_size kcs) in
  let info_byte = info_label_byte @< okm_len_byte in

  hkdf_expand kcs prk_out info_byte (hash_size kcs)

/// ---------------
/// Encryption Key
/// ---------------

let expand_k1 #kcs prk1e th1
  = let k1_len = aead_key_size kcs in
  let info_struct = construct_info info_label_k1 th1 k1_len in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk1e info_byte k1_len

let expand_k2 #kcs prk2e th2
  = let k2_len = aead_key_size kcs in
  let info_struct = construct_info info_label_k2 th2 k2_len in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk2e info_byte k2_len

let expand_k3 #kcs prk3e2m th3
  = let k3_len = aead_key_size kcs in
  let info_struct = construct_info info_label_k3 th3 k3_len in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk3e2m info_byte k3_len

let expand_k4 #kcs prk4e3m th4
  = let k4_len = aead_key_size kcs in
  let info_struct = construct_info info_label_k4 th4 k4_len in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk4e3m info_byte k4_len

/// ---------------
/// Initial Vector
/// ---------------

let expand_iv1 #kcs prk1e th1
  = let info_struct = construct_info info_label_iv1 th1 aead_iv_size in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk1e info_byte aead_iv_size

let expand_iv2 #kcs prk2e th2
  = let info_struct = construct_info info_label_iv2 th2 aead_iv_size in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk2e info_byte aead_iv_size

let expand_iv3 #kcs prk3e2m th3
  = let info_struct = construct_info info_label_iv3 th3 aead_iv_size in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk3e2m info_byte aead_iv_size

let expand_iv4 #kcs prk4e3m th4
  = let info_struct = construct_info info_label_iv4 th4 aead_iv_size in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk4e3m info_byte aead_iv_size

/// ---------------
/// SALT
/// ---------------

let expand_salt3e2m #kcs prk2e th2
  = let info_struct = construct_info info_label_salt3e2m th2 (hash_size kcs) in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk2e info_byte (hash_size kcs)

let expand_salt4e3m #kcs prk3e2m th3
  = let info_struct = construct_info info_label_salt4e3m th3 (hash_size kcs) in
  let info_byte = concat_info info_struct in
  hkdf_expand kcs prk3e2m info_byte (hash_size kcs)

/// ---------------
/// MAC
/// ---------------

let expand_mac2 #kcs prk3e2m ctx2
  = let ctx2_byte = concat_context2 #kcs ctx2 in
  let mac_len = mac23_size kcs in
  let info_struct = construct_info info_label_mac2 ctx2_byte mac_len in
  let info_byte = concat_info info_struct in 

  hkdf_expand kcs prk3e2m info_byte mac_len

let expand_mac3 #kcs prk4e3m ctx3
  = let ctx3_byte = concat_context3 #kcs ctx3 in
  let mac_len = mac23_size kcs in
  let info_struct = construct_info info_label_mac3 ctx3_byte mac_len in
  let info_byte = concat_info info_struct in

  hkdf_expand kcs prk4e3m info_byte mac_len