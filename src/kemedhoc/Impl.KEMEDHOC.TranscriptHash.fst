module Impl.KEMEDHOC.TranscriptHash

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
// module Spec = Spec.KEMEDHOC.TranscriptHash
friend Spec.KEMEDHOC.TranscriptHash

module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecParser = Spec.KEMEDHOC.Parser

open Spec.EDHOC.Serialization

/// Transcript Hash 1
let compute_th1 #kcs pk_X ct_auth_R th1
  = ST.push_frame ();
  let input_len = (kem_public_key_size_t kcs +! kem_ciphertext_size_t kcs) in
  let input_hash = create input_len (u8 0) in
  concat_buff2 pk_X ct_auth_R input_hash;

  do_hash kcs th1 input_len input_hash; 
  ST.pop_frame();
  ()

/// Transcript Hash 2
// #push-options "--z3rlimit 10"
let compute_th2 #kcs ct_y k_auth_I msg1 th2
  = (**) let h0 = ST.get () in
  ST.push_frame ();
  let msg1_len = concat_msg1_fixed_length_t kcs in
  let msg1_buffer = create msg1_len (u8 0) in
  concat_msg1 kcs msg1 msg1_buffer;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 msg1_buffer h0 h1);

  let msg1_hash_len = (size (SpecCrypto.hash_size kcs)) in
  let msg1_hash = create msg1_hash_len (u8 0) in
  do_hash kcs msg1_hash msg1_len msg1_buffer;
  (**) let h2 = ST.get () in
  (**) assert(modifies1 msg1_hash h1 h2);

  let input_len = kem_ciphertext_size_t kcs +! kem_shared_secret_size_t kcs +! msg1_hash_len in
  let input_hash = create input_len (u8 0) in
  concat_buff3 ct_y k_auth_I msg1_hash input_hash;
  (**) let h3 = ST.get () in
  (**) assert(modifies1 input_hash h2 h3);

  do_hash kcs th2 input_len input_hash;
  (**) let h4 = ST.get () in
  (**) assert(modifies1 th2 h3 h4);
  (**) assert(
    let msg1_s = message1_eval h0 msg1 in
    let msg1_concat_s = SpecParser.concat_msg1 msg1_s in
    let msg1_hash_s = SpecCrypto.do_hash kcs msg1_concat_s in
    // let input_hash_s = Seq.concat (Seq.concat (as_seq h0 ct_y) (as_seq h0 k_auth_I)) msg1_hash_s in
    let input_hash_s = (as_seq h0 ct_y) @< (as_seq h0 k_auth_I) @< msg1_hash_s in
    let th2_s = SpecCrypto.do_hash kcs input_hash_s in

    Seq.equal (as_seq h1 msg1_buffer) msg1_concat_s
    /\ Seq.equal (as_seq h2 msg1_hash) msg1_hash_s
    /\ Seq.equal (as_seq h3 input_hash) input_hash_s
    /\ Seq.equal (as_seq h4 th2) th2_s
  );

  ST.pop_frame ();
  ()
// #pop-options

let compute_th2_pre_hash #kcs ct_y k_auth_I msg1_hash th2
  = ST.push_frame ();
  (**) let h0 = ST.get () in

  let msg1_hash_len = size (SpecCrypto.hash_size kcs) in
  let input_len = kem_ciphertext_size_t kcs +! kem_shared_secret_size_t kcs +! msg1_hash_len in
  let input_hash = create input_len (u8 0) in
  concat_buff3 ct_y k_auth_I msg1_hash input_hash;
  (**) let h1 = ST.get () in

  do_hash kcs th2 input_len input_hash;
  (**) let h2 = ST.get () in
  (**) assert(
    let input_hash_s = (as_seq h0 ct_y) @< (as_seq h0 k_auth_I) @< (as_seq h0 msg1_hash) in
    Seq.equal (as_seq h1 input_hash) input_hash_s
  );

  ST.pop_frame ();
  ()

/// Transcript Hash 3
let compute_th3 #kcs th2 ptx2 cred_r th3
  = ST.push_frame ();
  (**) let h0 = ST.get () in

  let ptx2_buffer = create (plaintext2_size_t kcs) (u8 0) in
  concat_ptx2 kcs ptx2 ptx2_buffer;
  (**) let h1 = ST.get () in
  
  let input_len = (size (SpecCrypto.hash_size kcs)) +! (plaintext2_size_t kcs) +! (size SpecParser.cred_size) in
  let input_hash = create input_len (u8 0) in
  concat_buff3 th2 ptx2_buffer cred_r input_hash;
  (**) let h2 = ST.get () in

  do_hash kcs th3 input_len input_hash;
  (**) let h3 = ST.get () in
  (**) assert(
    let input_hash_s = (as_seq h0 th2) @< (SpecParser.concat_ptx2 (plaintext2_eval h0 ptx2)) @< (as_seq h0 cred_r) in

    Seq.equal (as_seq h2 input_hash) input_hash_s
  );

  ST.pop_frame ();
  ()

/// Transcript Hash 4
let compute_th4 #kcs th3 ptx3 cred_i th4
  = ST.push_frame ();
  (**) let h0 = ST.get () in

  let ptx3_buffer = create (plaintext3_size_t kcs) (u8 0) in
  concat_ptx3 kcs ptx3 ptx3_buffer;
  (**) let h1 = ST.get () in

  let input_len = (size (SpecCrypto.hash_size kcs)) +! (plaintext3_size_t kcs) +! (size SpecParser.cred_size) in
  let input_hash = create input_len (u8 0) in
  concat_buff3 th3 ptx3_buffer cred_i input_hash;
  (**) let h2 = ST.get () in

  do_hash kcs th4 input_len input_hash;
  (**) let h3 = ST.get () in
  (**) assert(
    let input_hash_s = (as_seq h0 th3) @< (SpecParser.concat_ptx3 (plaintext3_eval h0 ptx3)) @< (as_seq h0 cred_i) in

    Seq.equal (as_seq h2 input_hash) input_hash_s
  );
  ST.pop_frame ();
  ()