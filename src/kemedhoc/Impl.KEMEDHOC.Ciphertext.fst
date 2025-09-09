module Impl.KEMEDHOC.Ciphertext

module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecParser = Spec.KEMEDHOC.Parser
module SpecKS = Spec.KEMEDHOC.KeySchedule

friend Spec.KEMEDHOC.Ciphertext

/// -------------
/// Ciphertext 1
/// -------------
#push-options "--z3rlimit 10"
let encrypt_plaintext1 #kcs ptx1 th1 prk1e c1
  = ST.push_frame ();
  (**) let h0 = ST.get () in
  let hash_size = SpecCrypto.hash_size kcs in
  let aead_key_size = SpecCrypto.aead_key_size kcs in
  let iv_size = SpecCrypto.aead_iv_size in

  // derive K1
  let k1_buffer = create (size aead_key_size) (u8 0) in
  expand_k #kcs SpecKS.info_label_k1 prk1e th1 k1_buffer;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 k1_buffer h0 h1);

  // derive IV1
  let iv1_buffer = create (size iv_size) (u8 0) in
  expand_iv #kcs SpecKS.info_label_iv1 prk1e th1 iv1_buffer;
  (**) let h2 = ST.get () in
  (**) assert(modifies1 iv1_buffer h1 h2);

  // concat plaintext1
  let ptx1_buffer = create plaintext1_size_t (u8 0) in
  concat_ptx1 ptx1 ptx1_buffer;
  (**) let h3 = ST.get () in
  (**) assert(modifies1 ptx1_buffer h2 h3);

  let res = (aead_encrypt kcs k1_buffer (size iv_size) iv1_buffer (size hash_size) th1 plaintext1_size_t ptx1_buffer c1) in

  ST.pop_frame();
  res

let decrypt_ciphertext1 #kcs c1 th1 prk1e ptx1_buffer
  = ST.push_frame ();
  (**) let h0 = ST.get () in
  let hash_size = SpecCrypto.hash_size kcs in
  let aead_key_size = SpecCrypto.aead_key_size kcs in
  let iv_size = SpecCrypto.aead_iv_size in

  // derive K1
  let k1_buffer = create (size aead_key_size) (u8 0) in
  expand_k #kcs SpecKS.info_label_k1 prk1e th1 k1_buffer;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 k1_buffer h0 h1);

  // derive IV1
  let iv1_buffer = create (size iv_size) (u8 0) in
  expand_iv #kcs SpecKS.info_label_iv1 prk1e th1 iv1_buffer;
  (**) let h2 = ST.get () in
  (**) assert(modifies1 iv1_buffer h1 h2);

  let res = (aead_decrypt kcs k1_buffer (size iv_size) iv1_buffer (size hash_size) th1 plaintext1_size_t ptx1_buffer c1) in

  ST.pop_frame();
  res

/// -------------
/// Ciphertext 2
/// -------------
let encrypt_plaintext2 #kcs ptx2 th2 prk2e c2
  = ST.push_frame ();
  (**) let h0 = ST.get () in
  let hash_size = SpecCrypto.hash_size kcs in
  let aead_key_size = SpecCrypto.aead_key_size kcs in
  let iv_size = SpecCrypto.aead_iv_size in

  // derive K2
  let k2_buffer = create (size aead_key_size) (u8 0) in
  expand_k #kcs SpecKS.info_label_k2 prk2e th2 k2_buffer;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 k2_buffer h0 h1);

  // derive IV2
  let iv2_buffer = create (size iv_size) (u8 0) in
  expand_iv #kcs SpecKS.info_label_iv2 prk2e th2 iv2_buffer;
  (**) let h2 = ST.get () in
  (**) assert(modifies1 iv2_buffer h1 h2);

  // concat plaintext2
  let ptx2_buffer = create (plaintext2_size_t kcs) (u8 0) in
  concat_ptx2 kcs ptx2 ptx2_buffer;
  (**) let h3 = ST.get () in
  (**) assert(modifies1 ptx2_buffer h2 h3);

  let res = (aead_encrypt kcs k2_buffer (size iv_size) iv2_buffer (size hash_size) th2 (plaintext2_size_t kcs) ptx2_buffer c2) in

  ST.pop_frame();
  res

let decrypt_ciphertext2 #kcs c2 th2 prk2e ptx2_buffer
  = ST.push_frame ();
  (**) let h0 = ST.get () in
  let hash_size = SpecCrypto.hash_size kcs in
  let aead_key_size = SpecCrypto.aead_key_size kcs in
  let iv_size = SpecCrypto.aead_iv_size in

  // derive K2
  let k2_buffer = create (size aead_key_size) (u8 0) in
  expand_k #kcs SpecKS.info_label_k2 prk2e th2 k2_buffer;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 k2_buffer h0 h1);

  // derive IV2
  let iv2_buffer = create (size iv_size) (u8 0) in
  expand_iv #kcs SpecKS.info_label_iv2 prk2e th2 iv2_buffer;
  (**) let h2 = ST.get () in
  (**) assert(modifies1 iv2_buffer h1 h2);

  let res = (aead_decrypt kcs k2_buffer (size iv_size) iv2_buffer (size hash_size) th2 (plaintext2_size_t kcs) ptx2_buffer c2) in

  ST.pop_frame();
  res


/// -------------
/// Ciphertext 3
/// -------------
let encrypt_plaintext3 #kcs ptx3 th3 prk3e2m c3
  = ST.push_frame ();
  (**) let h0 = ST.get () in
  let hash_size = SpecCrypto.hash_size kcs in
  let aead_key_size = SpecCrypto.aead_key_size kcs in
  let iv_size = SpecCrypto.aead_iv_size in

  // derive K3
  let k3_buffer = create (size aead_key_size) (u8 0) in
  expand_k #kcs SpecKS.info_label_k3 prk3e2m th3 k3_buffer;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 k3_buffer h0 h1);

  // derive IV3
  let iv3_buffer = create (size iv_size) (u8 0) in
  expand_iv #kcs SpecKS.info_label_iv3 prk3e2m th3 iv3_buffer;
  (**) let h2 = ST.get () in
  (**) assert(modifies1 iv3_buffer h1 h2);

  // concat plaintext3
  let ptx3_buffer = create (plaintext3_size_t kcs) (u8 0) in
  concat_ptx3 kcs ptx3 ptx3_buffer;
  (**) let h3 = ST.get () in
  (**) assert(modifies1 ptx3_buffer h2 h3);

  let res = (aead_encrypt kcs k3_buffer (size iv_size) iv3_buffer (size hash_size) th3 (plaintext3_size_t kcs) ptx3_buffer c3) in

  ST.pop_frame();
  res

let decrypt_ciphertext3 #kcs c3 th3 prk3e2m ptx3_buffer
  = ST.push_frame();
  (**) let h0 = ST.get () in
  let hash_size = SpecCrypto.hash_size kcs in
  let aead_key_size = SpecCrypto.aead_key_size kcs in
  let iv_size = SpecCrypto.aead_iv_size in
  
  // derive K3
  let k3_buffer = create (size aead_key_size) (u8 0) in
  expand_k #kcs SpecKS.info_label_k3 prk3e2m th3 k3_buffer;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 k3_buffer h0 h1);

  // derive IV3
  let iv3_buffer = create (size iv_size) (u8 0) in
  expand_iv #kcs SpecKS.info_label_iv3 prk3e2m th3 iv3_buffer;
  (**) let h2 = ST.get () in
  (**) assert(modifies1 iv3_buffer h1 h2);

  let res = (aead_decrypt kcs k3_buffer (size iv_size) iv3_buffer (size hash_size) th3 (plaintext3_size_t kcs) ptx3_buffer c3) in

  ST.pop_frame();
  res

#pop-options