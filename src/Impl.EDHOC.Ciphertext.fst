module Impl.EDHOC.Ciphertext

module Seq = Lib.Sequence

(*LowStar modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq

module Spec = Spec.EDHOC.Ciphertext
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecParser = Spec.EDHOC.Parser
module SpecSerd = Spec.EDHOC.Serialization

friend Spec.EDHOC.Ciphertext

/// Ciphertext 2
let encrypt_plaintext2_mem #cs #auth_material #len_ptx2
  ptx2_mem th2_buff prk2e_buff ciphertext2_buff
  = ST.push_frame();
  let h0 = ST.get () in
  let ptx2_buff = create len_ptx2 (u8 0) in
  serialize_ptx2_mem ptx2_mem ptx2_buff;

  let k2_buff = create len_ptx2 (u8 0) in
  expand_keystream2 #cs prk2e_buff th2_buff len_ptx2 k2_buff;
  let h1 = ST.get () in

  xor_buffer ciphertext2_buff ptx2_buff k2_buff;

  ST.pop_frame()

let decrypt_ciphertext2 #cs #auth_material #len_c2 c2_buff
  th2_buff prk2e_buff p2_buff
  = ST.push_frame();
  let h0 = ST.get () in
  let k2_buff = create len_c2 (u8 0) in
  expand_keystream2 #cs prk2e_buff th2_buff len_c2 k2_buff;
  let h1 = ST.get () in

  xor_buffer p2_buff c2_buff k2_buff;

  ST.pop_frame()

/// Ciphertext 3
let encrypt_plaintext3 #cs #auth_material len_ptx3 ptx3_mem
  th3_buff prk3e2m_buff c3_buff
  = ST.push_frame();
  let h0 = ST.get () in

  // concatenate Plaintext3
  let ptx3_buff = create len_ptx3 (u8 0) in
  serialize_ptx3_mem ptx3_mem ptx3_buff;

  // derive K3
  let aead_key_size = size (SpecCrypto.aead_key_size (SpecCrypto.get_aead_alg cs)) in
  let k3_buff = create aead_key_size (u8 0) in
  expand_k3 #cs prk3e2m_buff th3_buff k3_buff;
  
  // derive IV3
  let iv_size = size (SpecCrypto.aead_iv_size) in
  let iv3_buff = create iv_size (u8 0) in
  expand_iv3 #cs prk3e2m_buff th3_buff iv3_buff;

  // AD3 = TH3
  let ad_size = size (SpecCrypto.hash_size cs) in
  let ad3_buff = th3_buff in
  let h1 = ST.get () in

  (**) assert( let a = SpecCrypto.get_aead_alg cs in
    let tag_size = SpecCrypto.aead_tag_size a in
    length c3_buff = size_v len_ptx3 + tag_size
    /\ length c3_buff <= max_size_t
    );
  let res = aead_encrypt cs k3_buff iv_size iv3_buff ad_size ad3_buff len_ptx3 ptx3_buff c3_buff in
  ST.pop_frame();
  res

let decrypt_ciphertext3 #cs #auth_material #len_c3 c3_buff
  th3_buff prk3e2m_buff p3_buff
  = ST.push_frame();
  let h0 = ST.get () in
  // derive K3
  let aead_key_size = size (SpecCrypto.aead_key_size (SpecCrypto.get_aead_alg cs)) in
  let k3_buff = create aead_key_size (u8 0) in
  expand_k3 #cs prk3e2m_buff th3_buff k3_buff;

  // derive IV3
  let iv_size = size (SpecCrypto.aead_iv_size) in
  let iv3_buff = create iv_size (u8 0) in
  expand_iv3 #cs prk3e2m_buff th3_buff iv3_buff;

  // AD3 = TH3
  let ad_size = size (SpecCrypto.hash_size cs) in
  let ad3_buff = th3_buff in
  let h1 = ST.get () in

  let p3_size = len_c3 -! size (SpecCrypto.aead_tag_size (SpecCrypto.get_aead_alg cs)) in

  let res = aead_decrypt cs k3_buff iv_size iv3_buff ad_size ad3_buff p3_size p3_buff c3_buff in
  ST.pop_frame();
  res