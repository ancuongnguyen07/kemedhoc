module Spec.KEMEDHOC.Ciphertext

open Spec.KEMEDHOC.KeySchedule

/// -------------
/// Ciphertext 1
/// -------------

let encrypt_plaintext1 #kcs ptx1 th1 prk1e
  = // derive K1
  let k1 = expand_k1 #kcs prk1e th1 in
  // derive IV1
  let iv1 = expand_iv1 #kcs prk1e th1 in
  // set up AEAD encryption params
  let ptx1_byte = concat_ptx1 ptx1 in
  aead_encrypt kcs k1 iv1 th1 ptx1_byte

let decrypt_ciphertext1 #kcs ciphertext1 th1 prk1e
  = // derive K1
  let k1 = expand_k1 #kcs prk1e th1 in
  // derive IV1
  let iv1 = expand_iv1 #kcs prk1e th1 in
  aead_decrypt kcs k1 iv1 th1 ciphertext1

let lemma_encrypt_decrypt_p1_correctness #kcs ptx1 th1 prk1e
  = ()

/// -------------
/// Ciphertext 2
/// -------------

let encrypt_plaintext2 #kcs ptx2 th2 prk2e
  = // derive K2
  let k2 = expand_k2 #kcs prk2e th2 in
  // derive IV2
  let iv2 = expand_iv2 #kcs prk2e th2 in
  let ptx2_byte = concat_ptx2 ptx2 in
  aead_encrypt kcs k2 iv2 th2 ptx2_byte

let decrypt_ciphertext2 #kcs ciphertext2 th2 prk2e
  = // derive K2
  let k2 = expand_k2 #kcs prk2e th2 in
  // derive IV2
  let iv2 = expand_iv2 #kcs prk2e th2 in
  aead_decrypt kcs k2 iv2 th2 ciphertext2

let lemma_encrypt_decrypt_p2_correctness #kcs ptx2 th2 prk2e
  = ()

/// -------------
/// Ciphertext 3
/// -------------

let encrypt_plaintext3 #kcs ptx3 th3 prk3e2m
  = // derive K3
  let k3 = expand_k3 #kcs prk3e2m th3 in
  // derive IV3
  let iv3 = expand_iv3 #kcs prk3e2m th3 in
  let ptx3_byte = concat_ptx3 ptx3 in
  aead_encrypt kcs k3 iv3 th3 ptx3_byte

let decrypt_ciphertext3 #kcs ciphertext3 th3 prk3e2m
  = // derive K3
  let k3 = expand_k3 #kcs prk3e2m th3 in
  // derive IV3
  let iv3 = expand_iv3 #kcs prk3e2m th3 in
  aead_decrypt kcs k3 iv3 th3 ciphertext3

let lemma_encrypt_decrypt_p3_correctness #kcs ptx3 th3 prk3e2m
  = ()