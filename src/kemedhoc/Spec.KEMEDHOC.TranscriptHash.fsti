module Spec.KEMEDHOC.TranscriptHash

open Spec.KEMEDHOC.Base.Definitions
open Spec.KEMEDHOC.CryptoPrimitives
open Spec.KEMEDHOC.Parser

module Seq = Lib.Sequence

/// Transcript Hash 1
/// TH1 = H(pk_X, ct_auth_R)
val compute_th1:
  #kcs: supportedKemCipherSuite
  -> pk_X: kemPublicKey kcs
  -> ct_auth_R: kemCiphertext kcs
  -> hash_out kcs

/// Transcript Hash 2
/// TH2 = H(ct_Y, K_auth_I, H(msg1))
val compute_th2:
  #kcs: supportedKemCipherSuite
  -> ct_y: kemCiphertext kcs
  -> k_auth_I: kemSharedSecret kcs
  -> msg1: message1 #kcs
  -> hash_out kcs

/// The hash of msg1 is pre-computed and passed as an argument
val compute_th2_pre_hash:
  #kcs: supportedKemCipherSuite
  -> ct_y: kemCiphertext kcs
  -> k_auth_I: kemSharedSecret kcs
  -> msg1_hash: hash_out kcs
  -> hash_out kcs

/// Lemmas
val lemma_compute_th2_equal_pre_hash:
  #kcs: supportedKemCipherSuite
  -> ct_y: kemCiphertext kcs
  -> k_auth_I: kemSharedSecret kcs
  -> msg1: message1 #kcs
  -> Lemma (ensures (
    let msg1_hash = do_hash kcs (concat_msg1 msg1) in
    let th2_pre_hash = compute_th2_pre_hash ct_y k_auth_I msg1_hash in
    let th2 = compute_th2 ct_y k_auth_I msg1 in

    Seq.equal th2 th2_pre_hash
  ))
  [SMTPat (compute_th2 ct_y k_auth_I msg1)]

/// Transcript Hash 3
/// TH3 = H(TH2, Ptx2, Cred_R)
val compute_th3:
  #kcs: supportedKemCipherSuite
  -> th2: hash_out kcs
  -> ptx2: plaintext2 #kcs
  -> cred_r: cred_byte
  -> hash_out kcs

/// Transcript Hash 4
/// TH4 = H(TH3, Ptx3, Cred_I)
val compute_th4:
  #kcs: supportedKemCipherSuite
  -> th3: hash_out kcs
  -> ptx3: plaintext3 #kcs
  -> cred_i: cred_byte
  -> hash_out kcs