module Spec.EDHOC.KeySchedule

module Seq = Lib.Sequence
open Lib.Sequence
open Lib.IntTypes
open Lib.ByteSequence

open Spec.EDHOC.CommonPred
open Spec.EDHOC.CryptoPrimitives
open Spec.EDHOC.Serialization
open Spec.EDHOC.Parser
// module Base = Spec.EDHOC.Base.Definitions
module FBytes = FStar.Bytes

(*-------------------- Key deriviation info constants*)
inline_for_extraction
let info_label_keystream2 = 0
inline_for_extraction
let info_label_salt3e2m = 1
inline_for_extraction
let info_label_mac2 = 2
inline_for_extraction
let info_label_k3 = 3
inline_for_extraction
let info_label_iv3 = 4
inline_for_extraction
let info_label_salt4e3m = 5
inline_for_extraction
let info_label_mac3 = 6
inline_for_extraction
let info_label_prk_out = 7
inline_for_extraction
let info_label_k4 = 8
inline_for_extraction
let info_label_iv4 = 9
inline_for_extraction
let info_label_prk_exporter = 10

(*---------------------------HKDF Info*)
val construct_info:
  label:info_label
  -> context:serializable_bytes
  -> okm_len:okm_len_type
  -> Tot info
val concat_info_get_length:
  i:info
  -> Tot size_nat
val concat_info:
  i:info
  -> Tot (lbytes (concat_info_get_length i))
val construct_info_to_bytes:
  label:info_label
  -> context:serializable_bytes
  -> okm_len:okm_len_type
  -> Tot (lbytes (
    (FBytes.repr_bytes label) + (length context) + (FBytes.repr_bytes okm_len)
  ))

let lemma_construct_info_to_bytes_equiv_concat
  (label:info_label) (context:serializable_bytes)
  (okm_len:okm_len_type)
  : Lemma (ensures (
    let info_bytes = construct_info_to_bytes label context okm_len in
    let info_struct = construct_info label context okm_len in
    equal info_bytes (concat_info info_struct)
  ))
  [SMTPat (construct_info_to_bytes label context okm_len)]
  = ()

// no need to deserialize this info struct
// as component fields are already-known to the caller.
val serialize_info_get_length:
  i:info
  -> Tot size_nat
val serialize_info:
  i:info
  -> Tot (r:lbytes (serialize_info_get_length i))

(*---------------------------Context2*)
val construct_context2:
  #cs:supported_cipherSuite
  -> c_r:c_id_bytes
  -> id_cred_r:id_cred_i_bytes
  -> th2:hash_out cs
  -> cred_r:cred_i_bytes
  // ead2 is an optional field
  -> ead2:option ead_bytes
  -> Tot (context2 #cs)

val concat_context2_get_length:
  #cs:supported_cipherSuite
  -> ctx2:context2 #cs
  -> Tot size_nat

val concat_context2:
  #cs:supported_cipherSuite
  -> ctx2:context2 #cs
  -> Tot (lbytes (concat_context2_get_length ctx2))

val construct_context2_to_bytes:
  #cs:supported_cipherSuite
  -> c_r:c_id_bytes
  -> id_cred_r:id_cred_i_bytes
  -> th2:hash_out cs
  -> cred_r:cred_i_bytes
  // ead2 is an optional field
  -> ead2:option ead_bytes
  -> Tot (lbytes (
    (length c_r) + (length id_cred_r) + (hash_size cs) + (length cred_r) + (
      match ead2 with
        | None -> 0
        | Some v -> length v
    )
  )) 

let lemma_construct_context2_to_bytes_equiv_concat
  (#cs:supported_cipherSuite) (c_r:c_id_bytes)
  (id_cred_r:id_cred_i_bytes) (th2:hash_out cs)
  (cred_r:cred_i_bytes) (ead2:option ead_bytes)
  : Lemma (ensures (
    let context2_bytes = construct_context2_to_bytes c_r id_cred_r th2 cred_r ead2 in
    let context2_struct = construct_context2 c_r id_cred_r th2 cred_r ead2 in
    equal context2_bytes (concat_context2 context2_struct)
  ))
  [SMTPat (construct_context2_to_bytes #cs c_r id_cred_r th2 cred_r ead2)]
  = ()

val serialize_context2_get_length:
  #cs:supported_cipherSuite
  -> ctx2:context2 #cs
  -> Tot size_nat
// no need to deserialize this context2 struct
// as component fields are already-known to the caller.
val serialize_context2:
  #cs:supported_cipherSuite
  -> ctx2:context2 #cs
  -> Tot (r:lbytes (serialize_context2_get_length ctx2))

(*---------------------------Context3*)
val construct_context3:
  #cs:supported_cipherSuite
  -> id_cred_i:id_cred_i_bytes
  -> th3:hash_out cs
  -> cred_i:cred_i_bytes
  -> ead3:option ead_bytes
  -> Tot (context3 #cs)

val concat_context3_get_length:
  #cs:supported_cipherSuite
  -> ctx3:context3 #cs
  -> Tot size_nat

val concat_context3:
  #cs:supported_cipherSuite
  -> ctx3:context3 #cs
  -> Tot (lbytes (concat_context3_get_length ctx3))

val construct_context3_to_bytes:
  #cs:supported_cipherSuite
  -> id_cred_i:id_cred_i_bytes
  -> th3:hash_out cs
  -> cred_i:cred_i_bytes
  -> ead3:option ead_bytes
  -> Tot (lbytes (
    (length id_cred_i) + (hash_size cs) + (length cred_i) + (
      match ead3 with
        | None -> 0
        | Some v -> length v
    )
  ))

let lemma_construct_context3_to_bytes_equiv_concat
  (#cs:supported_cipherSuite) (id_cred_i:id_cred_i_bytes)
  (th3:hash_out cs) (cred_i:cred_i_bytes) (ead3:option ead_bytes)
  : Lemma (ensures (
    let context3_bytes = construct_context3_to_bytes id_cred_i th3 cred_i ead3 in
    let context3_struct = construct_context3 id_cred_i th3 cred_i ead3 in
    equal context3_bytes (concat_context3 context3_struct)
  ))
  [SMTPat (construct_context3_to_bytes #cs id_cred_i th3 cred_i ead3)]
  = ()

val serialize_context3_get_length:
  #cs:supported_cipherSuite
  -> ctx3:context3 #cs
  -> Tot size_nat

// no need to deserialize this context3 struct
// as component fields are already-known to the caller.
val serialize_context3:
  #cs:supported_cipherSuite
  -> ctx3:context3 #cs
  -> Tot (lbytes (serialize_context3_get_length ctx3))


(*--------------------- PRK*)
val extract_prk2e:
  #cs:supported_cipherSuite
  -> th2:(hash_out cs) // salt
  -> g_xy:shared_secret cs // key
  -> hash_out cs

val extract_prk3e2m:
  #cs:supported_cipherSuite
  // -> prk2e:(hash_out cs)
  -> salt3e2m:(hash_out cs) // salt
  -> g_rx:shared_secret cs // key
  -> hash_out cs

let lemma_extract_prk3e2m_equality
  (#cs:supported_cipherSuite)
  (salt1:hash_out cs) (salt2:hash_out cs)
  (ikm1:shared_secret cs) (ikm2:shared_secret cs)
  : Lemma (requires (
    lbytes_eq salt1 salt2 /\ lbytes_eq ikm1 ikm2
  ))
  (ensures lbytes_eq (extract_prk3e2m salt1 ikm1) (extract_prk3e2m salt2 ikm2))
  = ()

val extract_prk4e3m:
  #cs:supported_cipherSuite
  -> salt4e3m:(hash_out cs) // salt
  -> g_iy:shared_secret cs // key
  -> hash_out cs

val expand_prk_out:
  #cs:supported_cipherSuite
  -> prk4e3m:(hash_out cs) // key
  -> th4:(hash_out cs) // info
  -> hash_out cs

val expand_prk_exporter:
  #cs:supported_cipherSuite
  -> prk_out:(hash_out cs) // key
  -> hash_out cs


(*---------------------- Encryption Key*)
val expand_keystream2:
  #cs:supported_cipherSuite
  -> prk2e:(hash_out cs) // key
  -> th2:(hash_out cs) // info
  -> ptx2_len:okm_len_type
  -> lbytes ptx2_len

val expand_k3:
  #cs:supported_cipherSuite
  -> prk3e2m:(hash_out cs) // key
  -> th3:(hash_out cs) // info
  -> aead_key cs


(*---------------------- Initial Vector*)
val expand_iv3:
  #cs:supported_cipherSuite
  -> prk3e2m:(hash_out cs) // key
  -> th3:(hash_out cs) // info
  -> aead_iv

(*---------------------- SALT*)
val expand_salt3e2m:
  #cs:supported_cipherSuite
  -> prk2e:(hash_out cs) // key
  -> th2:(hash_out cs) // info
  -> hash_out cs

val expand_salt4e3m:
  #cs:supported_cipherSuite
  -> prk3e2m:(hash_out cs) // key
  -> th3:(hash_out cs) // info
  -> hash_out cs

(*---------------------- MAC*)
val expand_mac2:
  #cs:supported_cipherSuite
  -> auth_mode:authentication_material
  -> prk3e2m:(hash_out cs) // key
  -> ctxt2:context2 #cs // info
  -> lbytes (mac23_size cs auth_mode)

val expand_mac3:
  #cs:supported_cipherSuite
  -> auth_mode:authentication_material
  -> prk4e3m:(hash_out cs) // key
  -> ctxt3:context3 #cs // info
  -> lbytes (mac23_size cs auth_mode)
