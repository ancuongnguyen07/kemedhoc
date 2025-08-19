module Impl.EDHOC.Core

open Lib.RawIntTypes
open Lib.ByteBuffer

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

friend Spec.EDHOC.Core
// friend Spec.EDHOC.Core.Lemmas

module Spec = Spec.EDHOC.Core
module SpecParser = Spec.EDHOC.Parser
module SpecDef = Spec.EDHOC.Base.Definitions

(*--------------------------- Common Things*)
/// Disjoint clauses
let hs_mem_disjoint_to_msg1_m (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs) (msg1_m:message1_mem #cs)
  = B.loc_disjoint (hs_mem_union_loc hs_m) (message1_mem_union_loc msg1_m)

let lemma_hs_mem_disjoint_to_msg1_m (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs) (msg1_m:message1_mem #cs)
  : Lemma (ensures (
    hs_mem_disjoint_to_msg1_m hs_m msg1_m ==> (
      match msg1_m with method_m, suite_i_m, g_x, c_i, ead1_m -> (
        hs_mem_disjoint_to hs_m method_m
        /\ hs_mem_disjoint_to hs_m suite_i_m
        /\ hs_mem_disjoint_to hs_m g_x /\ hs_mem_disjoint_to hs_m c_i
        /\ hs_mem_disjoint_to hs_m ead1_m
      )
    )
  ))
  [SMTPat (hs_mem_disjoint_to_msg1_m #cs hs_m msg1_m)]
  = ()


/// Initiate update HandShake state after Msg1
val init_hs_m:
  cs:SpecCrypto.supported_cipherSuite
  -> method_l:method_label
  -> hs_m:hs_mem #cs
  -> msg1_m:message1_mem #cs
  -> msg1_len:size_t
  -> g_x_m:ec_pub_key_buf cs
  -> ST.Stack unit
  (requires fun h0 ->
    msg1_len = message1_mem_get_length msg1_m
    /\ size_v msg1_len <= SpecCrypto.alg_get_hash_max_input (SpecCrypto.get_hash_alg cs)
    /\ is_valid_message1_mem_after_init h0 msg1_m
    /\ live h0 g_x_m /\ is_valid_message1_mem h0 msg1_m
    /\ is_valid_hs_mem h0 hs_m
    /\ hs_mem_disjoint_to hs_m g_x_m
    /\ hs_mem_disjoint_to_msg1_m hs_m msg1_m
    /\ (~(g_is_null hs_m.g_x) /\ ~(g_is_null hs_m.msg1_hash))
  )
  (ensures fun h0 _ h1 -> (
    is_legit_hs_mem h1 hs_m /\ is_valid_message1_mem_after_init h1 msg1_m
    /\ (
      modifies (loc hs_m.msg1_hash |+| loc hs_m.suite_i
                |+| loc hs_m.method |+| loc hs_m.g_x) h0 h1
    )
    /\ (
      let hs_abstract = eval_hs_mem h1 hs_m in
      let msg1_abstract = eval_message1_mem h0 msg1_m in
      let msg1_1_abstract = eval_message1_mem h1 msg1_m in
      let hash_msg1 = SpecCrypto.do_hash cs (SpecParser.concat_msg1 msg1_abstract) in
      let suite_i = SpecCrypto.get_supportedCipherSuite_label cs in

      suite_i = hs_abstract.suite_i
      /\ method_l = SpecDef.method_as_nat hs_abstract.method
      /\ Seq.equal hash_msg1 hs_abstract.msg1_hash
      /\ Seq.equal (as_seq h0 g_x_m) hs_abstract.g_x
      // post-condition that `msg1_m` has been unchanged!!!
      // this is IMPORTANT for proving further conditions in `initiator_send_msg1`
      /\ SpecParser.message1_compare msg1_abstract msg1_1_abstract
      /\ Seq.equal (as_seq h0 g_x_m) (as_seq h1 g_x_m)
    )
  ))

let init_hs_m cs method_l hs_m msg1_m msg1_len g_x_m
  = 
  // Push frame!!!
  ST.push_frame();
  (**) let hinit = ST.get () in
  let cs_label = (SpecCrypto.get_supportedCipherSuite_label cs) in

  // compute the hash of message1
  // and update the hash of message 1 inside `handshake_state`
  let msg1_concat_m = create msg1_len (u8 0) in
  concat_msg1_mem #cs msg1_m msg1_concat_m;
  do_hash cs (hs_m.msg1_hash) msg1_len msg1_concat_m;
  (**) let h1 = ST.get () in
  (**) assert(modifies2 hs_m.msg1_hash msg1_concat_m hinit h1);

  // // update `suite_i`
  upd (hs_m.suite_i) 0ul (u8 cs_label);
  (**) let h2 = ST.get () in
  (**) assert(modifies1 hs_m.suite_i h1 h2);

  // // update `method`
  upd (hs_m.method) 0ul (u8 method_l);
  (**) let h3 = ST.get () in
  (**) assert(let method_label = uint_to_nat (bget h3 hs_m.method 0) in
    method_label > 0 /\ method_label <= 4
  );
  (**) assert(modifies1 hs_m.method h2 h3);

  // update `g_x`
  copy (hs_m.g_x) g_x_m;
  (**) let h4 = ST.get() in
  (**) assert(modifies1 hs_m.g_x h3 h4);

  // Pop frame!!!
  ST.pop_frame();
  ()

(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)
let responder_process_msg1 #cs rs_m msg1_m msg1_len hs_m
  =
  (**) let hinit = ST.get () in
  let cs_label = (SpecCrypto.get_supportedCipherSuite_label cs) in
  let msg1_suite = (index (message1_mem_get_suite_i msg1_m) 0ul) in
  let rs_m_suite = (index (party_state_mem_get_suite rs_m) 0ul) in
  (**) let h_preinit = ST.get () in
  (**) assert(modifies0 hinit h_preinit);

  if (uint_to_nat msg1_suite <> uint_to_nat rs_m_suite)
  then CUnsupportedCipherSuite
  else (
    if (uint_to_nat msg1_suite <> cs_label)
    then CUnsupportedCipherSuite
    else (
      let g_x_m = message1_mem_get_g_x msg1_m in
      let method_m = index (message1_mem_get_method msg1_m) 0ul in
      init_hs_m cs (uint_to_nat method_m) hs_m msg1_m msg1_len g_x_m;

      // (**) let h0 = ST.get () in
      // (**) assert(modifies0 hinit h0);
      // // Push frame!!!
      // ST.push_frame();

      // // compute the hash of message1
      // // and update the hash of message 1 inside `hs_m`
      // let msg1_concat_m = create msg1_len (u8 0) in
      // concat_msg1_mem #cs msg1_m msg1_concat_m;
      // do_hash cs (hs_m.msg1_hash) msg1_len msg1_concat_m;
      // (**) let h1 = ST.get() in
      // (**) assert(modifies2 hs_m.msg1_hash msg1_concat_m h0 h1);

      // // assign suite for `hs_m`
      // upd hs_m.suite_i 0ul (u8 cs_label);
      // (**) let h2 = ST.get () in
      // (**) assert(modifies1 hs_m.suite_i h1 h2);

      // // assign method for `hs_m`. Copy 'method' from `msg1_m`
      // copy (hs_m.method) (message1_mem_get_method msg1_m);
      // (**) let h3 = ST.get () in
      // (**) assert(modifies1 hs_m.method h2 h3);

      // // assign g_x for `hs_m`. Copy 'g_x' from `msg1_m`
      // copy hs_m.g_x (message1_mem_get_g_x msg1_m);
      // (**) let h4 = ST.get () in
      // (**) assert(modifies1 hs_m.g_x h3 h4);

      // // Pop frame!!!
      // ST.pop_frame();
      // (**) let h5 = ST.get() in
      // (**) assert(~(live h5 msg1_concat_m));
      // (**) assert(
      //   let modified_loc = loc hs_m.msg1_hash |+| loc hs_m.suite_i
      //                   |+| loc hs_m.method |+| loc hs_m.g_x in
    
      //   modifies modified_loc h0 h5
      // );
      CSuccess
    )
  )

(*-------------------------------------------*)
(*---------------------------- Initiator side*)
(*-------------------------------------------*)

/// --------------------------------
/// Initiator Send Msg1
/// --------------------------------

/// Initiator construct Message1
val initiator_construct_msg1_m:
  cs:SpecCrypto.supported_cipherSuite
  -> method_l:method_label
  -> msg1_m:message1_mem #cs
  -> g_x_m:ec_pub_key_buf cs
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_message1_mem h0 msg1_m /\ live h0 entropy_p
    /\ message1_mem_disjoint_to msg1_m entropy_p
    /\ live h0 g_x_m /\ disjoint g_x_m entropy_p
    /\ message1_mem_disjoint_to msg1_m g_x_m
  )
  (ensures fun h0 _ h1 -> (
    is_valid_message1_mem_after_init h1 msg1_m
    /\ (
      modifies (message1_mem_union_loc_non_ead1 msg1_m |+| loc entropy_p) h0 h1
    )
    /\ (
      let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
      let e1_v = B.deref h1 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in

      let msg1_m_abtract = eval_message1_mem h1 msg1_m in

      let (entr1, c_i_random) = HACLRandom.crypto_random e0_v SpecParser.c_id_size in
      let suite_i = SpecCrypto.get_supportedCipherSuite_label cs in

      Ghost.reveal e1_v == entr1
      /\ Seq.equal c_i_random msg1_m_abtract.c_i
      /\ suite_i = msg1_m_abtract.suite_i
      /\ method_l = SpecDef.method_as_nat (msg1_m_abtract.method)
      /\ Seq.equal (as_seq h0 g_x_m) msg1_m_abtract.g_x
      /\ ~(Some? msg1_m_abtract.ead1)
      /\ Seq.equal (as_seq h0 g_x_m) (as_seq h1 g_x_m)
    )
  ))
  
let initiator_construct_msg1_m cs method_l msg1_m g_x_m
  = let hinit = ST.get () in
  (**) assert(method_l > 0 /\ method_l <= 4);
  let cs_label = (SpecCrypto.get_supportedCipherSuite_label cs) in
  // ------------------ construct `message1_mem`
  // randomly generate `c_id`
  let c_id_m = message1_mem_get_c_i msg1_m in
  (**) assert(disjoint c_id_m entropy_p);
  crypto_random c_id_m (size SpecParser.c_id_size);
  (**) let h1 = ST.get () in
  (**) assert(modifies2 c_id_m entropy_p hinit h1);

  // assign `suite_i` value
  upd (message1_mem_get_suite_i msg1_m) 0ul (u8 cs_label);
  (**) let h2 = ST.get () in
  (**) assert(modifies1 (message1_mem_get_suite_i msg1_m) h1 h2);

  // assign `g_x`
  (**) assert(
    let suite_i_label = uint_to_nat (bget h2 (message1_mem_get_suite_i msg1_m) 0) in
    suite_i_label >= 6 /\ suite_i_label <= 7
  );
  let msg1_gx = (message1_mem_get_g_x msg1_m) in
  copy msg1_gx g_x_m;
  (**) let h3 = ST.get () in
  (**) assert(modifies1 msg1_gx h2 h3);
  (**) assert(
    Seq.equal (as_seq h3 msg1_gx) (as_seq h1 g_x_m)
  );

  // assign method
  (**) let h0 = ST.get () in
  upd (message1_mem_get_method msg1_m) 0ul (u8 method_l);
  (**) let h1 = ST.get() in
  (**) assert(modifies1 (message1_mem_get_method msg1_m) h0 h1);

  // assign `ead1` as Null or leave it untouched
  (**) let h_msg1_x = ST.get () in
  (**) assert( let ead1_buff = message1_mem_get_ead1 msg1_m in
    g_is_null ead1_buff \/ length ead1_buff = 0);
  (**) assert(
    let method_label = uint_to_nat (bget h_msg1_x (message1_mem_get_method msg1_m) 0) in
    method_label > 0 /\ method_label <= 4
  );
  ()


/// Initiator composes Message1
#push-options "--z3rlimit 10"
let initiator_send_msg1 cs method_l msg1_m msg1_len is_m hs_m
  = (**) let h0 = ST.get () in
  let ekeypair_m = ps_mem_get_eph_keypair is_m in
  (**) assert(~(g_is_null_opt_ec_keypair_mem ekeypair_m));
  let epub_m = opt_ec_keypair_mem_get_pub ekeypair_m in
  let epriv_m = opt_ec_keypair_mem_get_priv ekeypair_m in
  (**) let suite_is_buff = ps_mem_get_suite_i is_m in
  let res_gen_key = generate_ec_keypair cs epriv_m epub_m in
  (**) let h_keygen = ST.get () in
  (**) assert(Seq.equal (as_seq h0 suite_is_buff) (as_seq h_keygen suite_is_buff));
  (**) assert(modifies (opt_ec_keypair_mem_union_loc ekeypair_m |+| loc entropy_p) h0 h_keygen);
  if (res_gen_key)
  then (
    // ------------------ construct `message1_mem`
    initiator_construct_msg1_m cs method_l msg1_m epub_m;

    // ------------------ update `handshake_state_mem`
    init_hs_m cs method_l hs_m msg1_m msg1_len epub_m;
    (**) let h = ST.get () in
    (**) assert(
      let hs_abstract = eval_hs_mem h hs_m in
      let msg1_abstract = eval_message1_mem h msg1_m in

      Seq.equal (nn_as_seq h epub_m) hs_abstract.g_x
      /\ Seq.equal (nn_as_seq h epub_m) msg1_abstract.g_x
    );
    (**) assert(
      Seq.equal (nn_as_seq h epriv_m) (nn_as_seq h_keygen epriv_m)
    );
    // (**) assert(
    //   Seq.equal (as_seq h0 suite_is_buff) (as_seq h suite_is_buff)
    // );

    // ------------------ update `party_state_mem`
    let cs_label = (SpecCrypto.get_supportedCipherSuite_label cs) in
    // update `eph_ec_keypair`
    // already updated at the key generation phase, at the beginning.

    (**) let h_end = ST.get () in
    (**) assert(
      let is_abstract = eval_party_state_mem h_end is_m in
      let keypair = Some?.v is_abstract.eph_ec_keypair in

      Seq.equal keypair.pub (nn_as_seq h_end epub_m)
      /\ Seq.equal keypair.priv (nn_as_seq h_end epriv_m)
    );
    /// unchanged assertation
    assert(
      let is_init_abstract = eval_party_state_mem h0 is_m in
      let is_end_abstract = eval_party_state_mem h_end is_m in

      Spec.ps_equal_non_shared_est #cs is_init_abstract is_end_abstract
    );
    assert(
      let is_end_abstract = eval_party_state_mem h_end is_m in
      let kp = Some?.v is_end_abstract.eph_ec_keypair in

      Seq.equal (nn_as_seq h epub_m) (nn_as_seq h_end epub_m)
      /\ Seq.equal (nn_as_seq h epriv_m) (nn_as_seq h_end epriv_m)
      /\ Seq.equal (nn_as_seq h_end epub_m) kp.pub
      /\ Seq.equal (nn_as_seq h_end epriv_m) kp.priv
    );

    CSuccess
  )
  else CInvalidECPoint
#pop-options

