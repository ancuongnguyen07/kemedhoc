module Spec.EDHOC.Ciphertext

(*HACL libs*)
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.EDHOC.Base.Definitions
open Spec.EDHOC.CryptoPrimitives
open Spec.EDHOC.Serialization
open Spec.EDHOC.Parser
open TypeHelper.EDHOC

/// Ciphertext2
val encrypt_plaintext2:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx2:plaintext2 #cs #auth_material
  -> th2:hash_out cs
  -> prk2e:hash_out cs
  -> Tot (lbytes (serialize_ptx2_get_length ptx2))

/// This function returns the raw bytes NOT serialized component fields.
/// Deserialization is responsible for callers.
val decrypt_ciphertext2:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ciphertext2:ciphertext2_bytes cs auth_material
  -> th2:hash_out cs
  -> prk2e:hash_out cs
  -> Tot (lbytes (length ciphertext2))

val lemma_ptx2_ciphertext2_equiv:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx2:plaintext2 #cs #auth_material
  -> th2:hash_out cs
  -> prk2e:hash_out cs
  -> Lemma
    (ensures (
      let c2 = encrypt_plaintext2 #cs #auth_material ptx2 th2 prk2e in
      let decrypted_text = decrypt_ciphertext2 #cs #auth_material c2 th2 prk2e in

      equal (serialize_ptx2 ptx2) decrypted_text
    ))
  [SMTPat (encrypt_plaintext2 #cs #auth_material ptx2 th2 prk2e)]

/// Ciphertext3
val encrypt_plaintext3:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  // -> len_ptx3:size_nat{len_ptx3 + aead_tag_size (get_aead_alg cs) <= max_size_t}
  -> ptx3:plaintext3 #cs #auth_material
  -> th3:hash_out cs
  -> prk3e2m:hash_out cs
  -> Tot (lbytes (serialize_ptx3_get_length ptx3 + aead_tag_size (get_aead_alg cs)))

/// This function returns the raw bytes NOT serialized component fields.
/// Deserialization is responsible for callers.
val decrypt_ciphertext3:
  #cs:supported_cipherSuite
  -> auth_material_i:authentication_material
  -> ciphertext3:aead_ciphertext_bytes cs
  -> th3:hash_out cs
  -> prk3e2m:hash_out cs
  -> Tot (eresult (lbytes (length ciphertext3 - aead_tag_size (get_aead_alg cs))))
  // -> Tot (eresult (plaintext3_bytes cs auth_material_i))

val lemma_encrypt_decrypt_ciphertext3_equiv:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx3:plaintext3 #cs #auth_material
  -> th3:hash_out cs
  -> prk3e2m:hash_out cs
  -> Lemma (ensures (
    let c3 = encrypt_plaintext3 #cs #auth_material ptx3 th3 prk3e2m in
    match (decrypt_ciphertext3 #cs auth_material c3 th3 prk3e2m) with
      | Fail DecryptionFailed -> True
      | Res decrypted_c3 -> (

        equal decrypted_c3 (serialize_ptx3 ptx3)
        /\ (
          let (id_cred_i, sig_or_mac3, ead3_op) = deserialize_ptx3_raw_bytes #cs #auth_material decrypted_c3 in
          let cred_i = id_cred_i in
          
          equal ptx3.id_cred_i id_cred_i
          /\ equal ptx3.sig_or_mac3 sig_or_mac3
        )
      )
      | _ -> False
  ))
  [SMTPat (encrypt_plaintext3 #cs #auth_material ptx3 th3 prk3e2m)]
