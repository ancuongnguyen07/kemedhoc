module Spec.EDHOC.Ciphertext

(*HACL libs*)
// open Lib.IntTypes
// open Lib.RawIntTypes
// open Lib.ByteSequence
// open Lib.Sequence

// open Spec.EDHOC.Base.Definitions
// open Spec.EDHOC.CryptoPrimitives
// open Spec.EDHOC.Serialization
// open Spec.EDHOC.Parser
open Spec.EDHOC.KeySchedule

module Seq = Lib.Sequence

module HACL_AEAD = Spec.Agile.AEAD

// friend Spec.EDHOC.Parser

/// Ciphertext2
let encrypt_plaintext2 #cs #auth_material ptx2 th2 prk2e
  = let serialized_ptx2 = serialize_ptx2 ptx2 in
  let ptx2_len = length serialized_ptx2 in
  // derive KEYSTREAM2
  let keystream2 = expand_keystream2 #cs prk2e th2 ptx2_len in
  xor keystream2 serialized_ptx2

let decrypt_ciphertext2 #cs #auth_material ciphertext2 th2 prk2e
  = let ciphertext2_len = length ciphertext2 in
  // derive KEYSTREAM2
  let keystream2 = expand_keystream2 #cs prk2e th2 ciphertext2_len in
  xor keystream2 ciphertext2

let lemma_ptx2_ciphertext2_equiv
  #cs #auth_material ptx2 th2 prk2e
  = let serialized_ptx2 = serialize_ptx2 ptx2 in
  let ptx2_len = length serialized_ptx2 in
  // derive KEYSTREAM2
  let keystream2 = expand_keystream2 #cs prk2e th2 ptx2_len in

  // let c2 = encrypt_plaintext2 ptx2 th2 prk2e in
  // let decrypted_text = decrypt_ciphertext2 #cs #auth_material c2 th2 prk2e in
  let c2 = xor serialized_ptx2 keystream2 in
  let decrypted_text = xor c2 keystream2 in
  lemma_xor_involution c2 keystream2;
  lemma_xor_involution serialized_ptx2 decrypted_text;
  lemma_xor_involution serialized_ptx2 keystream2;
  assert(equal decrypted_text serialized_ptx2)

/// Ciphertext3
let encrypt_plaintext3 #cs #auth_material ptx3 th3 prk3e2m
  = let serialized_ptx3 = serialize_ptx3 ptx3 in
  // derive K3
  let k3 = expand_k3 prk3e2m th3 in
  // derive IV3
  let iv3 = expand_iv3 prk3e2m th3 in
  // take AD3 = TH3 for AEAD encryption
  let ad3 = th3 in
  aead_encrypt k3 iv3 ad3 serialized_ptx3


let decrypt_ciphertext3 #cs auth_material_i ciphertext3 th3 prk3e2m
  = // derive K3
  let k3 = expand_k3 prk3e2m th3 in
  // derive IV3
  let iv3 = expand_iv3 prk3e2m th3 in
  // take AD3 = TH3 for AEAD encryption
  let ad3 = th3 in
  let serialized_ptx3_op = aead_decrypt k3 iv3 ad3 ciphertext3 in
  match serialized_ptx3_op with
    | None -> Fail DecryptionFailed
    | Some serialized_ptx3 -> (
      Res serialized_ptx3
    )
  
let lemma_encrypt_decrypt_ciphertext3_equiv #cs #auth_material
  ptx3 th3 prk3e2m
  = // derive K3
  let k3 = expand_k3 prk3e2m th3 in
  // derive IV3
  let iv3 = expand_iv3 prk3e2m th3 in
  // take AD3 = TH3 for AEAD encryption
  let ad3 = th3 in
  let serialized_ptx3 = serialize_ptx3 ptx3 in
  HACL_AEAD.correctness #(get_aead_alg cs) k3 iv3 ad3 serialized_ptx3;

  let (id_cred_i, sig_or_mac3, ead3)
      = deserialize_ptx3_raw_bytes #cs #auth_material serialized_ptx3 in
  assert(Seq.equal ptx3.id_cred_i id_cred_i);
  assert(Seq.equal ptx3.sig_or_mac3 sig_or_mac3);
  ()

