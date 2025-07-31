module Spec.EDHOC.TranscriptHash

open Spec.EDHOC.Base.Definitions
open Spec.EDHOC.CryptoPrimitives
open Spec.EDHOC.Parser

module Seq = Lib.Sequence

/// Transcript Hash 2
val compute_th2:
  #cs:supported_cipherSuite
  -> msg1:message1 #cs
  -> g_y:ec_pub_key cs
  -> hash_out cs

val compute_th2_pre_hash:
  #cs:supported_cipherSuite
  -> msg1_hash:hash_out cs
  -> g_y:ec_pub_key cs
  -> hash_out cs

let lemma_compute_th2_and_pre_hash_equiv
  (cs:supported_cipherSuite) (msg1:message1 #cs)
  (g_y:ec_pub_key cs)
  : Lemma (ensures (
    let msg1_hash = do_hash cs (concat_msg1 msg1) in
    Seq.equal (compute_th2 #cs msg1 g_y) (compute_th2_pre_hash #cs msg1_hash g_y)
  ))
  [SMTPat (compute_th2 #cs msg1 g_y)]
  = ()

/// Transcript Hash 3
val compute_th3:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> th2:hash_out cs
  -> ptx2:plaintext2 #cs #auth_material
  -> cred_r:cred_i_bytes
  -> hash_out cs

/// Transcript Hash 4
val compute_th4:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> th3:hash_out cs
  -> ptx3:plaintext3 #cs #auth_material
  -> cred_i:cred_i_bytes
  -> hash_out cs