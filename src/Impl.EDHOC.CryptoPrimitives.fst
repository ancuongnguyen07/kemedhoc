module Impl.EDHOC.CryptoPrimitives

(*The corresponding FStar high-level Spec*)
module Spec = Spec.EDHOC.CryptoPrimitives

// this module use OCaml crypto-kit.
// Remember to link with OCaml APIs when compile to C.
// look at `hacl-star/lib/ml/Lib_randomBuffer_System_gen.ml`
// open Lib.RandomSequence
// open Lib.RandomBuffer.System
module HACLRandom = Lib.RandomSequence

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence
module G = FStar.Ghost

module U32 = FStar.UInt32
module U64 = FStar.UInt64

(*AEAD*)
module SpecAEAD = Spec.Agile.AEAD
module ImplAEAD = EverCrypt.AEAD
module EverCryptError = EverCrypt.Error

(*Hash*)
module SpecHash = Spec.Agile.Hash
module ImplSHA2 = Hacl.Streaming.SHA2

(*HMAC*)
module ImplHMAC = Hacl.HMAC

(*HKDF*)
module SpecHKDF = Spec.Agile.HKDF
module ImplHKDF = Hacl.HKDF

(*DH and Signature related modules*)
module SpecDH = Spec.Agile.DH
friend Hacl.P256
module ImplP256 = Hacl.P256
// friend ImplP256
module ImplEDSA25519 = Hacl.Ed25519
// friend ImplEDSA25519
module ImplCurve25519_51 = Hacl.Curve25519_51

(*Utilities*)
// open TypeHelper.EDHOC
open Impl.EDHOC.Utilities

friend Spec.EDHOC.CryptoPrimitives

(*----------------------------------------------------*)
#push-options "--z3rlimit 10 --max_fuel 8 --max_ifuel 8"
(*------------------ DH*)
let secret_to_public #cs priv pub
  = match (Spec.get_ec_alg cs) with
    | SpecDH.DH_Curve25519 -> (
      ImplCurve25519_51.secret_to_public pub priv;
      true
    )
    | SpecDH.DH_P256 -> (
      ImplP256.dh_initiator pub priv
    )

/// parameter order of `P256.dh_responder` is `out, pub, priv`
/// which is not consistent to the order across my implementation
/// so I tweak a little bit here to make it consistent
let my_P256_dh_responder
  (output:lbuffer uint8 (size 64)) (priv:lbuffer uint8 (size 32))
  (pub:lbuffer uint8 (size 64))
  : ST.Stack bool
  (requires fun h0 ->
    live h0 output /\ live h0 priv /\ live h0 pub
    /\ disjoint output priv /\ disjoint priv pub /\ disjoint output pub
  )
  (ensures fun h0 res h1 -> modifies1 output h0 h1
    /\ (
      let ecdh_shared = (Spec.P256.ecdh (as_seq h0 pub) (as_seq h0 priv)) in
      (res <==> Some? ecdh_shared) /\ (res ==> as_seq h1 output == Some?.v ecdh_shared)
    )
  )
  = ImplP256.dh_responder output pub priv

let dh #cs output priv pub
  = match (Spec.get_ec_alg cs) with
    | SpecDH.DH_Curve25519 -> (
      // parameters order of `Curve25519_51.ecdh` is `out, priv, pub`
      ImplCurve25519_51.ecdh output priv pub
    )
    | SpecDH.DH_P256 -> (
      my_P256_dh_responder output priv pub
    )

(*------------------ AEAD*)

/// ----------------- AEAD Encryption
/// AES256_GCM
let aead_aes256_gcm_encrypt key iv_len iv ad_len ad ptx_len ptx ctxt
  = ST.push_frame();
  let h0 = ST.get () in
  let tag_len = (Spec.aead_tag_size SpecAEAD.AES256_GCM) in
  let cipher_buffer:lbuffer uint8 ptx_len = sub ctxt 0ul ptx_len in
  let tag_buffer:aead_tag_lbuffer SpecAEAD.AES256_GCM
    = sub ctxt ptx_len (size tag_len) in
  // let (cipher_buffer, tag_buffer) = split_buffer ctxt ptx_len in
  let h1 = ST.get () in
  assert(Seq.equal h1.[|ctxt|] (Seq.concat h1.[|cipher_buffer|] h1.[|tag_buffer|]));

  // NOTE!: `ImplAEAD.encrypt_expand_aes256_gcm_no_check` does not check hardware
  // configuration for AES implementation in runtime. Making sure the config was
  // compliant.
  //
  // `ImplAEAD.encrypt_expand_aes256_gcm` does check in runtime. -> no need `pre`
  // in the `aead_encrypt_st`
  // Read more at: https://github.com/hacl-star/hacl-star/blob/main/providers/evercrypt/EverCrypt.AEAD.fsti#L419
  let res = ImplAEAD.encrypt_expand_aes256_gcm key iv iv_len
              ad ad_len ptx ptx_len cipher_buffer tag_buffer in
  assert(res == EverCryptError.Success \/ res == EverCryptError.UnsupportedAlgorithm);
  let h2 = ST.get () in
  assert(Seq.equal (as_seq h2 ctxt) (Seq.concat (as_seq h2 cipher_buffer) (as_seq h2 tag_buffer)));
  ST.pop_frame();
  evercrypt_err_to_c_response res

/// AES128_GCM
let aead_aes128_gcm_encrypt key iv_len iv ad_len ad ptx_len ptx ctxt
  = ST.push_frame();
  let h0 = ST.get () in
  let tag_len = (Spec.aead_tag_size SpecAEAD.AES128_GCM) in
  let cipher_buffer:lbuffer uint8 ptx_len = sub ctxt 0ul ptx_len in
  let tag_buffer:aead_tag_lbuffer SpecAEAD.AES128_GCM
    = sub ctxt ptx_len (size tag_len) in
  // let (cipher_buffer, tag_buffer) = split_buffer ctxt ptx_len in
  let h1 = ST.get () in
  assert(Seq.equal h1.[|ctxt|] (Seq.concat h1.[|cipher_buffer|] h1.[|tag_buffer|]));

  // NOTE!: `ImplAEAD.encrypt_expand_aes128_gcm_no_check` does not check hardware
  // configuration for AES implementation in runtime. Making sure the config was
  // compliant.
  //
  // `ImplAEAD.encrypt_expand_aes128_gcm` does check in runtime. -> no need `pre`
  // in the `aead_encrypt_st`
  // Read more at: https://github.com/hacl-star/hacl-star/blob/main/providers/evercrypt/EverCrypt.AEAD.fsti#L419
  let res = ImplAEAD.encrypt_expand_aes128_gcm key iv iv_len
              ad ad_len ptx ptx_len cipher_buffer tag_buffer in

  assert(res == EverCryptError.Success \/ res == EverCryptError.UnsupportedAlgorithm);
  let h2 = ST.get () in
  assert(Seq.equal (as_seq h2 ctxt) (Seq.concat (as_seq h2 cipher_buffer) (as_seq h2 tag_buffer)));
  ST.pop_frame();
  evercrypt_err_to_c_response res

/// ----------------- AEAD Decryption
/// AES256_GCM
let aead_aes256_gcm_decrypt key iv_len iv ad_len ad ptx_len ptx ctxt
  = ST.push_frame();
  let h0 = ST.get () in
  let tag_len = Spec.aead_tag_size SpecAEAD.AES256_GCM in
  let cipher_buffer:lbuffer uint8 ptx_len = sub ctxt 0ul ptx_len in
  let tag_buffer:aead_tag_lbuffer SpecAEAD.AES256_GCM
    = sub ctxt ptx_len (size tag_len) in
  let h1 = ST.get () in
  (**) assert(Seq.equal h1.[|ctxt|] (Seq.concat h1.[|cipher_buffer|] h1.[|tag_buffer|]));

  // NOTE!: `ImplAEAD.decrypt_expand_aes256_gcm_no_check` does not check hardware
  // configuration for AES implementation in runtime. Making sure the config was
  // compliant.
  //
  // `ImplAEAD.decrypt_expand_aes256_gcm` does check in runtime. -> no need `pre`
  // in the `aead_decrypt_st`
  // Read more at: https://github.com/hacl-star/hacl-star/blob/main/providers/evercrypt/EverCrypt.AEAD.fsti#L419
  let res = ImplAEAD.decrypt_expand_aes256_gcm key iv iv_len
            ad ad_len cipher_buffer ptx_len tag_buffer ptx in
  (**) let h2 = ST.get () in
  (**) assert(res == EverCryptError.Success \/ res == EverCryptError.AuthenticationFailure
      \/ res == EverCryptError.UnsupportedAlgorithm);
  (**) assert(Seq.equal (as_seq h2 ctxt) (Seq.concat (as_seq h2 cipher_buffer) (as_seq h2 tag_buffer)));
  (**) assert(res == EverCryptError.UnsupportedAlgorithm ==> modifies0 h1 h2);

  ST.pop_frame();
  evercrypt_err_to_c_response res

/// AES128_GCM
let aead_aes128_gcm_decrypt key iv_len iv ad_len ad ptx_len ptx ctxt
  = ST.push_frame();
  let h0 = ST.get () in
  let tag_len = Spec.aead_tag_size SpecAEAD.AES128_GCM in
  let cipher_buffer:lbuffer uint8 ptx_len = sub ctxt 0ul ptx_len in
  let tag_buffer:aead_tag_lbuffer SpecAEAD.AES128_GCM
    = sub ctxt ptx_len (size tag_len) in
  let h1 = ST.get () in
  (**) assert(Seq.equal h1.[|ctxt|] (Seq.concat h1.[|cipher_buffer|] h1.[|tag_buffer|]));

  // NOTE!: `ImplAEAD.decrypt_expand_aes128_gcm_no_check` does not check hardware
  // configuration for AES implementation in runtime. Making sure the config was
  // compliant.
  //
  // `ImplAEAD.decrypt_expand_aes128_gcm` does check in runtime. -> no need `pre`
  // in the `aead_decrypt_st`
  // Read more at: https://github.com/hacl-star/hacl-star/blob/main/providers/evercrypt/EverCrypt.AEAD.fsti#L419
  let res = ImplAEAD.decrypt_expand_aes128_gcm key iv iv_len
            ad ad_len cipher_buffer ptx_len tag_buffer ptx in
  (**) let h2 = ST.get () in
  (**) assert(res == EverCryptError.Success \/ res == EverCryptError.AuthenticationFailure
      \/ res == EverCryptError.UnsupportedAlgorithm);
  (**) assert(Seq.equal (as_seq h2 ctxt) (Seq.concat (as_seq h2 cipher_buffer) (as_seq h2 tag_buffer)));
  (**) assert(res == EverCryptError.UnsupportedAlgorithm ==> modifies0 h1 h2);
  
  ST.pop_frame();
  evercrypt_err_to_c_response res

(*-------------------- Hash*)
let hash_sha2_256 output input_len input
  = ImplSHA2.hash_256 output input input_len;
  ()

(*-------------------- HMAC*)
let hmac_sha2_256 output key_len key data_len data
  = ImplHMAC.compute_sha2_256 output key key_len data data_len;
  ()

(*-------------------- HKDF*)
/// ----------------- HKDF Expand
let hkdf_expand_sha2_256 okm_len okm prk_len prk info_len info
  = ImplHKDF.expand_sha2_256 okm prk prk_len info info_len okm_len;
  ()

/// ----------------- HKDF Extract
let hkdf_extract_sha2_256 prk_out salt_len salt ikm_len ikm
  = ImplHKDF.extract_sha2_256 prk_out salt salt_len ikm ikm_len;
  ()

(*-------------------- EC signature scheme*)
/// Split P256-based signature
let split_P256_signature sig
  = split_buffer sig 32ul

/// EC-Signing
let ecdsa_sign cs signature op_nonce msg_len msg priv
  = match (Spec.get_signature_alg cs) with
    | SpecDH.DH_P256 -> (
      assert(Some? op_nonce);
      let ha = Spec.get_hash_alg cs in
      ImplP256.ecdsa_signature (Spec.P256.Hash ha) signature msg_len msg priv (Some?.v op_nonce)
    )
    | SpecDH.DH_Curve25519 -> (
      assert(not (Some? op_nonce));
      ImplEDSA25519.sign signature priv msg_len msg;
      true
    )

/// EC-Verification
let ecdsa_verify cs msg_len msg pub signature
  = match (Spec.get_signature_alg cs) with
    | SpecDH.DH_P256 -> (
      ST.push_frame();
      let h0 = ST.get () in
      assert(length pub = 64);
      let ha = Spec.get_hash_alg cs in
      // let (sig_r, sig_s) = split_P256_signature signature in
      let sig_r:lbuffer uint8 (size 32) = sub signature 0ul 32ul in
      let sig_s:lbuffer uint8 (size 32) = sub signature 32ul 32ul in
      let h1 = ST.get () in
      assert(Seq.equal (as_seq h0 signature) (Seq.concat (as_seq h1 sig_r) (as_seq h1 sig_s)));

      let res = ImplP256.ecdsa_verification (Spec.P256.Hash ha) msg_len msg pub sig_r sig_s in

      ST.pop_frame();
      res
    )
    | SpecDH.DH_Curve25519 -> (
      assert(length pub = 32);
      ImplEDSA25519.verify pub msg_len msg signature
    )

(*-------------------- XOR*)
let xor_buffer #len output b1 b2
  = ST.push_frame();
  let h0 = ST.get () in
  map2T len output (logxor #U8 #SEC) b1 b2;
  let h1 = ST.get () in
  assert(as_seq h1 output == Seq.map2 (logxor #U8 #SEC) (as_seq h0 b1) (as_seq h0 b2));
  ST.pop_frame();
  ()

(*-------------------- Generate key pairs*)
let generate_ec_keypair cs priv pub
  = 
  // recall (entropy_p <: buffer (G.erased entropy));
  recall entropy_p;
  ST.push_frame();
  (**) let h0 = ST.get () in
  (**) assert(length priv = 32);
  crypto_random priv 32ul;
  let res = secret_to_public #cs priv pub in
  (**) let h1 = ST.get () in
  (**) let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
  (**) assert(
    let (e1, buf_v) = (HACLRandom.crypto_random e0_v 32) in
    let res_pub_abstract = Spec.secret_to_public #cs buf_v in

    Seq.equal (as_seq h1 priv) buf_v
    /\ (res <==> Some? res_pub_abstract)
    /\ (res ==> Seq.equal (as_seq h1 pub) (Some?.v res_pub_abstract))
  );
  ST.pop_frame();
  res

#pop-options