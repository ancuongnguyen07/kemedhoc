module Impl.EDHOC.TranscriptHash

friend Spec.EDHOC.TranscriptHash

module Seq = Lib.Sequence

(*LowStar modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq

module Buffer = Lib.Buffer

module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecParser = Spec.EDHOC.Parser
module SpecSerd = Spec.EDHOC.Serialization

open Impl.EDHOC.CryptoPrimitives
open Impl.EDHOC.Utilities

/// Transcript Hash 2 (TH2) with pre-hashed Msg1
let compute_th2_pre_hash_mem #cs msg1_hash_m g_y_mem th2_buff
  = ST.push_frame();
  let g_y_len = pub_key_size_v cs in
  let msg1_hash_buff_len = (size (hash_size cs)) in

  let msg1_g_y_concat_len = (msg1_hash_buff_len +! g_y_len) in
  let msg1_g_y_concat = create msg1_g_y_concat_len (u8 0) in

  concat_buff2 msg1_hash_m g_y_mem msg1_g_y_concat;
  do_hash cs th2_buff msg1_g_y_concat_len msg1_g_y_concat;

  ST.pop_frame();
  ()

/// Transcript Hash 2 (TH2) with Msg1
let compute_th2_mem #cs #msg1_mem_len msg1_mem g_y_mem th2_buff
  = let h0 = ST.get () in
  // Hash the message1
  ST.push_frame();
  let msg1_hash_buff_len = (size (hash_size cs)) in
  let msg1_hash_buff = create msg1_hash_buff_len (u8 0) in
  let msg1_mem_concat_buff = create msg1_mem_len (u8 0) in

  concat_msg1_mem #cs msg1_mem msg1_mem_concat_buff;
  do_hash cs msg1_hash_buff msg1_mem_len msg1_mem_concat_buff;
  let h1 = ST.get () in
  
  // Hash the hash of message1 and g_y
  let g_y_len = pub_key_size_v cs in
  let msg1_g_y_concat_len = (msg1_hash_buff_len +! g_y_len) in
  let msg1_g_y_concat = create msg1_g_y_concat_len (u8 0) in

  concat_buff2 msg1_hash_buff g_y_mem msg1_g_y_concat;
  do_hash cs th2_buff msg1_g_y_concat_len msg1_g_y_concat;
  let h2 = ST.get () in
  (**) assert(
    let msg1_abstract = eval_message1_mem #cs h0 msg1_mem in
    let msg1_abstract_concat = SpecParser.concat_msg1 #cs msg1_abstract in
    let msg1_abstract_hash = SpecCrypto.do_hash cs msg1_abstract_concat in
    let g_y = as_seq h0 g_y_mem in

    let msg1_abstract_hash_g_y_concat = Seq.concat msg1_abstract_hash g_y in
    let th2 = SpecCrypto.do_hash cs msg1_abstract_hash_g_y_concat in

    Seq.equal msg1_abstract_hash (as_seq h2 msg1_hash_buff)
    /\ Seq.equal msg1_abstract_hash_g_y_concat (as_seq h2 msg1_g_y_concat)
    /\ Seq.equal th2 (as_seq h2 th2_buff)
  );
  ST.pop_frame()

/// Transcript Hash 3 (TH3)
let compute_th3_mem #cs auth_material th2_buff ptx2_mem cred_r_buff th3_buff
  = let h0 = ST.get () in
  ST.push_frame();
  let len_ptx2 = plaintext2_len_fixed_v cs auth_material in
  (**) assert(len_ptx2 = plaintext2_mem_get_length ptx2_mem);
  // concatenate all components in plaintext2
  let ptx2_concat_buff = create len_ptx2 (u8 0) in
  concat_ptx2_mem #cs #auth_material #len_ptx2 ptx2_mem ptx2_concat_buff;
  let h1 = ST.get () in

  // concatenation of the hash input
  let concat_len = len_ptx2 +! (size (hash_size cs)) +! (size SpecParser.cred_size) in
  let hash_input_concat = create concat_len (u8 0) in
  concat_buff3 th2_buff ptx2_concat_buff cred_r_buff hash_input_concat;

  do_hash cs th3_buff concat_len hash_input_concat;
  let h2 = ST.get () in
  (**) assert(
    let ptx2_abstract = plaintext2_mem_to_plaintext2 h0 ptx2_mem in
    let ptx2_lbytes = SpecParser.concat_ptx2 ptx2_abstract in
    let cred_r = as_seq h0 cred_r_buff in
    let th2 = as_seq h0 th2_buff in
    let hash_input = Seq.concat th2 (Seq.concat ptx2_lbytes cred_r) in
    let th3 = SpecCrypto.do_hash cs hash_input in

    Seq.equal hash_input (as_seq h2 hash_input_concat)
    /\ Seq.equal th3 (as_seq h2 th3_buff)
  );

  ST.pop_frame()

/// Transcript Hash 4 (TH4)
let compute_th4_mem #cs auth_material th3_buff ptx3_mem cred_i_buff th4_buff
  = let h0 = ST.get () in
  ST.push_frame();
  let len_ptx3 = plaintext3_len_fixed_v cs auth_material in
  (**) assert(len_ptx3 = plaintext3_mem_get_length ptx3_mem); 
  // concatenate all components of plaintext3
  let ptx3_concat_buff = create len_ptx3 (u8 0) in
  concat_ptx3_mem ptx3_mem ptx3_concat_buff;
  let h1 = ST.get () in

  // concatenation of the hash input
  let concat_len = len_ptx3 +! (size (hash_size cs)) +! (size SpecParser.cred_size) in
  let hash_input_concat = create concat_len (u8 0) in
  concat_buff3 th3_buff ptx3_concat_buff cred_i_buff hash_input_concat;

  do_hash cs th4_buff concat_len hash_input_concat;
  let h2 = ST.get () in
  (**) assert(
    let ptx3_abstract = plaintext3_mem_to_plaintext3 h0 ptx3_mem in
    let ptx3_lbytes = SpecParser.concat_ptx3 ptx3_abstract in
    let cred_i = as_seq h0 cred_i_buff in
    let th3 = as_seq h0 th3_buff in
    let hash_input = Seq.concat th3 (Seq.concat ptx3_lbytes cred_i) in
    let th4 = SpecCrypto.do_hash cs hash_input in

    Seq.equal hash_input (as_seq h2 hash_input_concat)
    /\ Seq.equal th4 (as_seq h2 th4_buff)
  );

  ST.pop_frame()