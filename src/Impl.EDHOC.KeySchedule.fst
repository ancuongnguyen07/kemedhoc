module Impl.EDHOC.KeySchedule

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence
module FBytes = FStar.Bytes

friend Spec.EDHOC.KeySchedule

module Spec = Spec.EDHOC.KeySchedule
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecSerd = Spec.EDHOC.Serialization

(*
HKDF Info, Context 2, and Context 3 related functions
are defined in `Impl.EDHOC.Parser`
*)

/// ------------------------
/// PRK
/// ------------------------

/// PRK2e
let extract_prk2e #cs th2_buff g_xy_buff prk2e_buff
  = hkdf_extract cs prk2e_buff (size (SpecCrypto.hash_size cs)) th2_buff
                (size (SpecCrypto.shared_secret_size cs)) g_xy_buff

/// PRK3e2m
let extract_prk3e2m #cs salt3e2m_buff g_rx_buff prk3e2m_buff
  = hkdf_extract cs prk3e2m_buff (size (SpecCrypto.hash_size cs)) salt3e2m_buff
                (size (SpecCrypto.shared_secret_size cs)) g_rx_buff

/// PRK4e3m
let extract_prk4e3m #cs salt4e3m_buff g_iy_buff prk4e3m_buff
  = hkdf_extract cs prk4e3m_buff (size (SpecCrypto.hash_size cs)) salt4e3m_buff
                (size (SpecCrypto.shared_secret_size cs)) g_iy_buff

/// PRK_out
let expand_prk_out #cs prk4e3m_buff th4_buff prk_out_buff
  = let h0 = ST.get () in
  ST.push_frame();
  // create HKDF info buffer
  let hash_size = (size (SpecCrypto.hash_size cs)) in
  let okm_len = hash_size in
  let info_len = 1ul +! hash_size +! 1ul in
  let info_buff = create info_len (u8 0) in
  let label_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul label_buff Spec.info_label_prk_out;
  let okm_len_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul okm_len_buff (size_v okm_len);
  let context_buff = th4_buff in
  // let hkdf_info_mem = construct_info_mem label_buff context_buff okm_len_buff in
  // concat_info_mem hash_size 1ul hkdf_info_mem info_buff;
  concat_buff3 label_buff context_buff okm_len_buff info_buff;
  let h1 = ST.get () in

  // Proof-purposed only
  // Aligning with `info_mem` struct for modelling
  (**) assert(Seq.equal (SpecSerd.nat_to_bytes Spec.info_label_prk_out) (as_seq h1 label_buff)
    /\ Seq.equal (SpecSerd.nat_to_bytes (size_v okm_len)) (as_seq h1 okm_len_buff));
  (**) assert(
    let info_struct_bytes = Spec.construct_info_to_bytes Spec.info_label_prk_out (as_seq h0 context_buff) (size_v okm_len) in
    Seq.equal (info_struct_bytes) (as_seq h1 info_buff)
  );

  // do HKDF expand
  hkdf_expand cs okm_len prk_out_buff hash_size prk4e3m_buff info_len info_buff;
  ST.pop_frame()

/// PRK_exporter
let expand_prk_exporter #cs prk_out_buff prk_exporter_buff
  = let h0 = ST.get () in
  ST.push_frame();
  // create HKDF info buffer
  let hash_size = size (SpecCrypto.hash_size cs) in
  let okm_len = hash_size in
  let info_len = 1ul +! 1ul in
  let info_buff = create info_len (u8 0) in
  let label_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul label_buff Spec.info_label_prk_exporter;
  let okm_len_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul okm_len_buff (size_v okm_len);
  // In this case, `context_buff` is an empty byte,
  // should it be explicitly declared as a NULL?
  // let context_buff = null in
  concat_buff2 label_buff okm_len_buff info_buff;
  let h1 = ST.get () in

  // Proofs
  (**) assert(Seq.equal (SpecSerd.nat_to_bytes Spec.info_label_prk_exporter) (as_seq h1 label_buff)
    /\ Seq.equal (SpecSerd.nat_to_bytes (size_v okm_len)) (as_seq h1 okm_len_buff));
  (**) assert(
    let info_struct_bytes
      = Seq.concat (as_seq h1 label_buff) (as_seq h1 okm_len_buff) in
    Seq.equal info_struct_bytes (as_seq h1 info_buff)
  );

  // do HKDF_expand
  hkdf_expand cs okm_len prk_exporter_buff hash_size prk_out_buff info_len info_buff;

  ST.pop_frame()

/// ------------------------
/// Encryption key
/// ------------------------

/// KEYSTREAM2
let expand_keystream2 #cs prk2e_buff th2_buff ptx2_len k2_buff
  =
  ST.push_frame();
  let hash_size = size (SpecCrypto.hash_size cs) in
  let okm_len = ptx2_len in
  let okm_len_size = (size (FBytes.repr_bytes (size_v okm_len))) in
  let info_len = 1ul +! hash_size +! okm_len_size in
  let info_buff = create info_len (u8 0) in
  let label_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul label_buff Spec.info_label_keystream2;
  let okm_len_buff = create okm_len_size (u8 0) in
  nat_to_bytes okm_len_size okm_len_buff (size_v okm_len);

  let context_buff = th2_buff in
  let h0 = ST.get () in
  concat_buff3 label_buff context_buff okm_len_buff info_buff;
  let h1 = ST.get () in

  // Proofs
  (**) assert(Seq.equal (SpecSerd.nat_to_bytes Spec.info_label_keystream2) (as_seq h1 label_buff)
    /\ Seq.equal (SpecSerd.nat_to_bytes (size_v okm_len)) (as_seq h1 okm_len_buff));
  (**) assert(
    let info_struct_bytes
      = Spec.construct_info_to_bytes Spec.info_label_keystream2 (as_seq h0 context_buff) (size_v okm_len) in
    Seq.equal info_struct_bytes (as_seq h1 info_buff)
  );

  // do HKDF_expand
  hkdf_expand cs okm_len k2_buff hash_size prk2e_buff info_len info_buff;

  ST.pop_frame()

/// K3
let expand_k3 #cs prk3e2m_buff th3_buff k3_buff 
  = ST.push_frame();
  let hash_size = size (SpecCrypto.hash_size cs) in
  let okm_len = size (SpecCrypto.aead_key_size (SpecCrypto.get_aead_alg cs)) in
  let okm_len_size = size (FBytes.repr_bytes (size_v okm_len)) in

  let label_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul label_buff Spec.info_label_k3;
  let okm_len_buff = create okm_len_size (u8 0) in
  nat_to_bytes okm_len_size okm_len_buff (size_v okm_len);
  let context_buff = th3_buff in
  
  let info_len = 1ul +! hash_size +! okm_len_size in
  let info_buff = create info_len (u8 0) in
  let h0 = ST.get () in

  concat_buff3 label_buff context_buff okm_len_buff info_buff;
  let h1 = ST.get () in

  // Proofs
  (**) assert(Seq.equal (SpecSerd.nat_to_bytes Spec.info_label_k3) (as_seq h0 label_buff)
    /\ Seq.equal (SpecSerd.nat_to_bytes (size_v okm_len)) (as_seq h0 okm_len_buff));
  (**) assert(
    let info_struct_bytes
      = Spec.construct_info_to_bytes Spec.info_label_k3 (as_seq h0 context_buff) (size_v okm_len) in
    Seq.equal info_struct_bytes (as_seq h1 info_buff)
  );

  // do HKDF_expand
  hkdf_expand cs okm_len k3_buff hash_size prk3e2m_buff info_len info_buff;

  ST.pop_frame()

/// IV3
let expand_iv3 #cs prk3e2m_buff th3_buff iv3_buff
  = ST.push_frame();
  let hash_size = size (SpecCrypto.hash_size cs) in
  let okm_len = size (SpecCrypto.aead_iv_size) in
  let okm_len_size = size (FBytes.repr_bytes (size_v okm_len)) in

  let label_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul label_buff Spec.info_label_iv3;
  let okm_len_buff = create okm_len_size (u8 0) in
  nat_to_bytes okm_len_size okm_len_buff (size_v okm_len);
  let context_buff = th3_buff in

  let info_len = 1ul +! hash_size +! okm_len_size in
  let info_buff = create info_len (u8 0) in
  let h0 = ST.get () in

  concat_buff3 label_buff context_buff okm_len_buff info_buff;
  let h1 = ST.get () in

  // Proofs
  (**) assert(Seq.equal (SpecSerd.nat_to_bytes Spec.info_label_iv3) (as_seq h0 label_buff)
    /\ Seq.equal (SpecSerd.nat_to_bytes (size_v okm_len)) (as_seq h0 okm_len_buff));
  (**) assert(
    let info_struct_bytes
      = Spec.construct_info_to_bytes Spec.info_label_iv3 (as_seq h0 context_buff) (size_v okm_len) in
    Seq.equal info_struct_bytes (as_seq h1 info_buff)
  );

  // do HKDF_expand
  hkdf_expand cs okm_len iv3_buff hash_size prk3e2m_buff info_len info_buff;

  ST.pop_frame()

/// SALT3e2m
let expand_salt3e2m #cs prk2e_buff th2_buff salt3e2m_buff
  = ST.push_frame();
  let hash_size = size (SpecCrypto.hash_size cs) in
  let okm_len = hash_size in

  let label_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul label_buff Spec.info_label_salt3e2m;
  let okm_len_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul okm_len_buff (size_v okm_len);
  let context_buff = th2_buff in

  let info_len = 1ul +! hash_size +! 1ul in
  let info_buff = create info_len (u8 0) in
  let h0 = ST.get () in

  concat_buff3 label_buff context_buff okm_len_buff info_buff;
  let h1 = ST.get () in

  // Proofs
  (**) assert(Seq.equal (SpecSerd.nat_to_bytes Spec.info_label_salt3e2m) (as_seq h0 label_buff)
    /\ Seq.equal (SpecSerd.nat_to_bytes (size_v okm_len)) (as_seq h0 okm_len_buff));
  (**) assert(
    let info_struct_bytes
      = Spec.construct_info_to_bytes Spec.info_label_salt3e2m (as_seq h0 context_buff) (size_v okm_len) in
    Seq.equal info_struct_bytes (as_seq h1 info_buff)
  );

  // do HKDF_expand
  hkdf_expand cs okm_len salt3e2m_buff hash_size prk2e_buff info_len info_buff;

  ST.pop_frame()

/// SALT4e3m
let expand_salt4e3m #cs prk3e2m_buff th3_buff salt4e3m_buff
  = ST.push_frame();
  let hash_size = size (SpecCrypto.hash_size cs) in
  let okm_len = hash_size in

  let label_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul label_buff Spec.info_label_salt4e3m;
  let okm_len_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul okm_len_buff (size_v okm_len);
  let context_buff = th3_buff in

  let info_len = 1ul +! hash_size +! 1ul in
  let info_buff = create info_len (u8 0) in
  let h0 = ST.get () in

  concat_buff3 label_buff context_buff okm_len_buff info_buff;
  let h1 = ST.get () in

  // Proofs
  (**) assert(Seq.equal (SpecSerd.nat_to_bytes Spec.info_label_salt4e3m) (as_seq h0 label_buff)
    /\ Seq.equal (SpecSerd.nat_to_bytes (size_v okm_len)) (as_seq h0 okm_len_buff));
  (**) assert(
    let info_struct_bytes
      = Spec.construct_info_to_bytes Spec.info_label_salt4e3m (as_seq h0 context_buff) (size_v okm_len) in
    Seq.equal info_struct_bytes (as_seq h1 info_buff)
  );

  // do HKDF expand
  hkdf_expand cs okm_len salt4e3m_buff hash_size prk3e2m_buff info_len info_buff;

  ST.pop_frame()

/// MAC_2
let expand_mac2 #cs auth_material prk3e2m_buff context2 mac2_buff
  = ST.push_frame();
  let h0 = ST.get () in
  let hash_size = size (SpecCrypto.hash_size cs) in
  let okm_len = size (SpecCrypto.mac23_size cs auth_material) in
  // This implementation does not support EAD2
  let len_ctx2 = size (SpecParser.c_id_size + SpecParser.id_cred_size +
                (SpecCrypto.hash_size cs) + SpecParser.cred_size) in
  (**) assert(len_ctx2 = context2_mem_get_length context2);
  
  let context2_buff = create len_ctx2 (u8 0) in
  concat_context2_mem context2 context2_buff;

  let label_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul label_buff Spec.info_label_mac2;
  let okm_len_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul okm_len_buff (size_v okm_len);

  let info_len = 1ul +! len_ctx2 +! 1ul in
  let info_buff = create info_len (u8 0) in
  let h1 = ST.get () in

  concat_buff3 label_buff context2_buff okm_len_buff info_buff;
  let h2 = ST.get () in

  (**) assert(
    let info_struct_bytes
      = Spec.construct_info_to_bytes Spec.info_label_mac2 (as_seq h1 context2_buff) (size_v okm_len) in
    Seq.equal info_struct_bytes (as_seq h2 info_buff)
  );

  // do HKDF_expand
  hkdf_expand cs okm_len mac2_buff hash_size prk3e2m_buff info_len info_buff;

  ST.pop_frame()

/// MAC_3
let expand_mac3 #cs auth_material prk4e3m_buff context3 mac3_buff
  = ST.push_frame();
  let h0 = ST.get () in
  let hash_size = size (SpecCrypto.hash_size cs) in
  let okm_len = size (SpecCrypto.mac23_size cs auth_material) in

  let len_ctx3 = size (SpecParser.id_cred_size + (SpecCrypto.hash_size cs)
                        + SpecParser.cred_size ) in
  (**) assert(len_ctx3 = context3_mem_get_length context3);

  let context3_buff = create len_ctx3 (u8 0) in
  concat_context3_mem context3 context3_buff;

  let label_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul label_buff (Spec.info_label_mac3);
  let okm_len_buff = create 1ul (u8 0) in
  nat_to_bytes 1ul okm_len_buff (size_v okm_len);

  let info_len = 1ul +! len_ctx3 +! 1ul in
  let info_buff = create info_len (u8 0) in
  let h1 = ST.get () in

  concat_buff3 label_buff context3_buff okm_len_buff info_buff;
  let h2 = ST.get () in

  (**) assert(
    let info_struct_bytes
      = Spec.construct_info_to_bytes Spec.info_label_mac3 (as_seq h1 context3_buff) (size_v okm_len) in
    Seq.equal info_struct_bytes (as_seq h2 info_buff)
  );

  // do HKDF_expand
  hkdf_expand cs okm_len mac3_buff hash_size prk4e3m_buff info_len info_buff;

  ST.pop_frame()