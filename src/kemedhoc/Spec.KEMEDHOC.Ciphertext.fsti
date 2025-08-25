module Spec.KEMEDHOC.Ciphertext

/// HACL libs
open Lib.IntTypes
open Lib.ByteSequence
module Seq = Lib.Sequence

open Spec.KEMEDHOC.CryptoPrimitives
open Spec.KEMEDHOC.Parser

/// -------------
/// Ciphertext 1
/// -------------

val encrypt_plaintext1:
  #kcs: supportedKemCipherSuite
  -> ptx1: plaintext1
  -> th1: hash_out kcs
  -> prk1e: hash_out kcs
  -> lbytes (concat_ptx1_get_length ptx1 + aead_tag_size kcs)

val decrypt_ciphertext1:
  #kcs: supportedKemCipherSuite
  -> ciphertext1: lbytes (c1_size kcs)
  -> th1: hash_out kcs
  -> prk1e: hash_out kcs
  -> option (lbytes (Seq.length ciphertext1 - aead_tag_size kcs))

val lemma_encrypt_decrypt_p1_correctness:
  #kcs: supportedKemCipherSuite
  -> ptx1: plaintext1
  -> th1: hash_out kcs
  -> prk1e: hash_out kcs
  -> Lemma (ensures (
    let c1 = encrypt_plaintext1 #kcs ptx1 th1 prk1e in
    match (decrypt_ciphertext1 #kcs c1 th1 prk1e) with
      | None -> False
      | Some decrypted_text ->
        Seq.equal (concat_ptx1 ptx1) decrypted_text
  ))
  [SMTPat (encrypt_plaintext1 #kcs ptx1 th1 prk1e)]

/// -------------
/// Ciphertext 2
/// -------------

val encrypt_plaintext2:
  #kcs: supportedKemCipherSuite
  -> ptx2: plaintext2 #kcs
  -> th2: hash_out kcs
  -> prk2e: hash_out kcs
  -> lbytes (concat_ptx2_get_length ptx2 + aead_tag_size kcs)

val decrypt_ciphertext2:
  #kcs: supportedKemCipherSuite
  -> ciphertext2: lbytes (c2_size kcs)
  -> th2: hash_out kcs
  -> prk2e: hash_out kcs
  -> option (lbytes (Seq.length ciphertext2 - aead_tag_size kcs))

val lemma_encrypt_decrypt_p2_correctness:
  #kcs: supportedKemCipherSuite
  -> ptx2: plaintext2 #kcs
  -> th2: hash_out kcs
  -> prk2e: hash_out kcs
  -> Lemma (ensures (
    let c2 = encrypt_plaintext2 #kcs ptx2 th2 prk2e in
    match (decrypt_ciphertext2 #kcs c2 th2 prk2e) with
      | None -> False
      | Some decrypted_text ->
        Seq.equal (concat_ptx2 ptx2) decrypted_text
  ))
  [SMTPat (encrypt_plaintext2 #kcs ptx2 th2 prk2e)]

/// -------------
/// Ciphertext 3
/// -------------

val encrypt_plaintext3:
  #kcs: supportedKemCipherSuite
  -> ptx3: plaintext3 #kcs
  -> th3: hash_out kcs
  -> prk3e2m: hash_out kcs
  -> lbytes (concat_ptx3_get_length ptx3 + aead_tag_size kcs)

val decrypt_ciphertext3:
  #kcs: supportedKemCipherSuite
  -> ciphertext3: lbytes (c3_size kcs)
  -> th3: hash_out kcs
  -> prk3e2m: hash_out kcs
  -> option (lbytes (Seq.length ciphertext3 - aead_tag_size kcs))

val lemma_encrypt_decrypt_p3_correctness:
  #kcs: supportedKemCipherSuite
  -> ptx3: plaintext3 #kcs
  -> th3: hash_out kcs
  -> prk3e2m: hash_out kcs
  -> Lemma (ensures (
    let c3 = encrypt_plaintext3 #kcs ptx3 th3 prk3e2m in
    match (decrypt_ciphertext3 #kcs c3 th3 prk3e2m) with
      | None -> False
      | Some decrypted_text ->
        Seq.equal (concat_ptx3 ptx3) decrypted_text
  ))
  [SMTPat (encrypt_plaintext3 #kcs ptx3 th3 prk3e2m)]