module Impl.EDHOC.Core.Msg2

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
module SpecKS = Spec.EDHOC.KeySchedule
module SpecTH = Spec.EDHOC.TranscriptHash
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecEncDec = Spec.EDHOC.Ciphertext

// open Spec.EDHOC.CryptoPrimitives

#push-options "--z3rlimit 25 --max_fuel 4"
(*-------------------------------------------*)
(*---------------------------- Initiator side*)
(*-------------------------------------------*)
let initiator_process_msg2 #cs local_auth_material remote_auth_material is_m hs_m msg2_m
  = let hinit = ST.get () in

  /// push frame!!!
  ST.push_frame();
  /// Allocation: create all gonna-be-neccessary buffers here
  let c2_m = message2_mem_get_ciphertext2 msg2_m in
  let ptx2_len = plaintext2_len_fixed_v cs remote_auth_material in
  (**) assert(size_v ptx2_len = length c2_m);
  let p2_m = create ptx2_len (u8 0) in

  /// Still allocation: fields for Context2
  let c_r_m = create (size SpecParser.c_id_size) (u8 0) in
  let id_cred_r_m = create (size SpecParser.id_cred_size) (u8 0) in
  let cred_r_m = id_cred_r_m in
  let sig_or_mac2_m = create (sig_or_mac23_size_v cs remote_auth_material) (u8 0) in
  let ead2_m = null #MUT #uint8 in

  /// Still allocation: MAC2
  let mac2_len = (mac23_size_v cs remote_auth_material) in
  let mac2_m = create mac2_len (u8 0) in


  // retrieve G_Y from Message 2
  let g_y_m = message2_mem_get_g_y msg2_m in
  // retrieve X from the party_state
  let x_m = opt_ec_keypair_mem_get_priv (ps_mem_get_eph_keypair is_m) in
  (**) assert(~(g_is_null x_m));
  (**) assert(B.all_disjoint [loc g_y_m; loc x_m; loc hs_m.g_xy]);
  // compute the shared secret G_XY
  let res_dh = dh #cs hs_m.g_xy x_m g_y_m in

  if (not res_dh)
  then (
    ST.pop_frame();

    CInvalidECPoint
  )
  else (
    (**) let h1 = ST.get () in
    (**) assert(
      let g_y = as_seq hinit g_y_m in
      let x = nn_as_seq hinit x_m in
      let res_abstract = SpecCrypto.dh #cs x g_y in

      modifies1 hs_m.g_xy hinit h1
      /\ (Some? res_abstract <==> res_dh)
      /\ (Some? res_abstract ==> (
        Seq.equal (Some?.v res_abstract) (as_seq h1 hs_m.g_xy)
      ))
    );

    let id_cred_i_m = party_state_mem_get_id is_m in
    let cred_i_m = party_state_mem_get_id is_m in

    // compute TH2
    let th2_m = hs_m.th2 in
    compute_th2_pre_hash_mem #cs hs_m.msg1_hash g_y_m th2_m;
    (**) let h2 = ST.get () in
    (**) assert(
      let msg1_hash = as_seq h1 hs_m.msg1_hash in
      let g_y = as_seq h1 g_y_m in
      let th2 = SpecTH.compute_th2_pre_hash #cs msg1_hash g_y in

      modifies1 th2_m h1 h2
      /\ Seq.equal th2 (as_seq h2 th2_m)
    );

    // derive PRK2e
    extract_prk2e #cs th2_m hs_m.g_xy hs_m.prk2e;
    (**) let h3 = ST.get () in
    (**) assert(
      let th2 = as_seq h2 th2_m in
      let g_xy = as_seq h2 hs_m.g_xy in
      let prk2e = SpecKS.extract_prk2e #cs th2 g_xy in

      modifies1 hs_m.prk2e h2 h3
      /\ Seq.equal prk2e (as_seq h3 hs_m.prk2e)
    );

    // decrypt Ciphertext2
    decrypt_ciphertext2 #cs #remote_auth_material #ptx2_len c2_m th2_m hs_m.prk2e p2_m;
    (**) let h4 = ST.get() in
    (**) assert(
      let c2 = as_seq h3 c2_m in
      let th2 = as_seq h3 th2_m in
      let prk2e = as_seq h3 hs_m.prk2e in
      let p2 = SpecEncDec.decrypt_ciphertext2 #cs #remote_auth_material c2 th2 prk2e in

      modifies1 p2_m h3 h4
      /\ Seq.equal p2 (as_seq h4 p2_m)
    );

    // deserialize Plaintext2
    deserialize_ptx2_mem cs remote_auth_material p2_m c_r_m id_cred_r_m sig_or_mac2_m ead2_m;
    (**) let h5 = ST.get () in
    (**) assert(
      let (c_r, id_cred_r, sig_or_mac2, ead2)
        = SpecParser.deserialize_ptx2_raw_bytes cs remote_auth_material
          (as_seq h4 p2_m) in

      Seq.equal c_r (as_seq h5 c_r_m)
      /\ Seq.equal id_cred_r (as_seq h5 id_cred_r_m)
      /\ Seq.equal sig_or_mac2 (as_seq h5 sig_or_mac2_m)
    );

    // derive PRK3e2m
    let g_r_m = ps_mem_get_remote_static_pub is_m in
    let x_m = opt_ec_keypair_mem_get_priv (ps_mem_get_eph_keypair is_m) in
    (**) assert(~(g_is_null x_m));
    let res_prk3e2m = derive_prk3e2m #cs remote_auth_material hs_m.prk2e hs_m.th2
                      x_m g_r_m hs_m.prk3e2m in
    (**) let h6 = ST.get () in
    (**) assert(res_prk3e2m == CSuccess \/ res_prk3e2m == CInvalidECPoint);
    (**) assert(
      let g_r = as_seq h5 g_r_m in
      let x = nn_as_seq h5 x_m in
      let th2 = as_seq h5 hs_m.th2 in
      let prk2e = as_seq h5 hs_m.prk2e in
      let res_prk3e2m_spec = Spec.derive_prk3e2m #cs remote_auth_material prk2e th2
        (Some x) (Some g_r) in

      (res_prk3e2m == CSuccess \/ res_prk3e2m == CInvalidECPoint)
      /\ (Res? res_prk3e2m_spec <==> res_prk3e2m == CSuccess)
      /\ (res_prk3e2m == CSuccess ==> Seq.equal (match res_prk3e2m_spec with
                                      Res prk3e2m -> prk3e2m) (as_seq h6 hs_m.prk3e2m)
                  /\ modifies1 hs_m.prk3e2m h5 h6
    ));



    if (res_prk3e2m <> CSuccess)
    then (
        ST.pop_frame();

        CInvalidECPoint
      )
    else (
        // construct context2
        let context2_m = construct_context2_mem #cs c_r_m id_cred_r_m th2_m cred_r_m ead2_m in
        (**) let h6 = ST.get () in
        (**) assert(live h6 ead2_m);
        (**) assert(B.all_disjoint [loc c_r_m; loc id_cred_r_m; loc th2_m; loc ead2_m]);
        (**) assert(is_valid_context2_mem h6 context2_m);

        /// The below steps for verifying Sig_or_mac2

        expand_mac2 #cs remote_auth_material hs_m.prk3e2m context2_m mac2_m;
        (**) let h7 = ST.get () in

        let pk_r_m = ps_mem_get_remote_sig_pub is_m in
        let is_valid_sig_or_mac2
          = verify_sig_or_mac2 #cs remote_auth_material sig_or_mac2_m mac2_m context2_m pk_r_m in
        (**) let h8 = ST.get () in
        (**) assert(modifies0 h7 h8);

        if (not is_valid_sig_or_mac2)
        then (
          ST.pop_frame();

          CIntegrityCheckFailed
        )
        else (
          /// Check if the Responder's credential is identical to the Initiator's credential
          /// this check prevents Reflection Attack.
          if (lbytes_eq cred_i_m cred_r_m)
          then (
            ST.pop_frame();
            CInvalidCredential
          )
          else (
            /// And check if the received credential in the local list of Initiator.
            if (not (lbytes_eq (ps_mem_get_remote_id_cred is_m) cred_r_m))
            then (
              ST.pop_frame();
              CUnknownCredentialID
            )
            else (
              ST.pop_frame();
              CSuccess
            )
          )
        )

        // ST.pop_frame();
        // CSuccess
      )

    // ST.pop_frame();
    // CSuccess

  )
#pop-options

(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)
#restart-solver
#push-options "--z3rlimit 20 --max_fuel 4"
let responder_send_msg2 #cs #auth_material #ptx2_len #msg2_len ptx2_buff
  msg2_buff rs_m hs_m
  =
  /// Push frame!!!
  ST.push_frame();
  let hinit = ST.get () in

  /// Allocates all gonna-be-needed values here at the beginning
  /// to avoid difficulties to prove through stateful branching.
  /// Allocation: connection ID
  let c_r_m = create (size SpecParser.c_id_size) (u8 0) in

  /// Allocation: MAC2
  let mac2_len = (mac23_size_v cs auth_material) in
  let mac2_m = create mac2_len (u8 0) in

  /// Allocation: SIG_OR_MAC2
  let sig_or_mac2_len = (sig_or_mac23_size_v cs auth_material) in
  let sig_or_mac2_m = create sig_or_mac2_len (u8 0) in

  /// Allocation: Plaintext2
  let ptx2_len = plaintext2_len_fixed_v cs auth_material in
  let ptx2_buff = create ptx2_len (u8 0) in

  /// Allocation: Ciphertext2
  let ciphertext2_m = create ptx2_len (u8 0) in

  let ekeypair_m = ps_mem_get_eph_keypair rs_m in
  (**) assert(~(g_is_null_opt_ec_keypair_mem ekeypair_m));
  let epub_m = opt_ec_keypair_mem_get_pub ekeypair_m in
  let epriv_m = opt_ec_keypair_mem_get_priv ekeypair_m in
  (**) assert(B.all_disjoint [loc epub_m; loc epriv_m; loc entropy_p; loc hs_m.msg1_hash]);
  (**) assert(~(g_is_null epub_m) /\ ~(g_is_null epriv_m));

  // G_Y and Y generation
  let res_keygen = generate_ec_keypair cs epriv_m epub_m in
  (**) let h0 = ST.get () in
  (**) assert(modifies3 epub_m epriv_m entropy_p hinit h0);

  if (not res_keygen)
  then (
    /// Pop frame!!!
    ST.pop_frame();

    // if key generation failed
    CInvalidECPoint
  )
  else (

    // key generation succeeded
    (**) let h1 = ST.get () in
    (**) assert(
      let ev_0 = B.deref hinit (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
      let ev_1 = B.deref h1 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
      // do assertation regarding `generate_ec_keypair`
      let res_keygen_spec = SpecCrypto.generate_ec_keypair cs ev_0 in

      (Some? res_keygen_spec <==> res_keygen)
      /\ (res_keygen ==> (
        let (keypair, entr) = Some?.v res_keygen_spec in

        Ghost.reveal ev_1 == entr
        /\ Seq.equal keypair.pub (nn_as_seq h1 epub_m)
        /\ Seq.equal keypair.priv (nn_as_seq h1 epriv_m)
      ))
    );
    (**) assert(Seq.equal (as_seq hinit hs_m.msg1_hash) (as_seq h1 hs_m.msg1_hash));

    // randomly generate `c_r`
    // let c_r_m = plaintext2_mem_get_c_r ptx2_m in
    (**) assert(disjoint c_r_m hs_m.msg1_hash);
    crypto_random c_r_m (size SpecParser.c_id_size);
    (**) let h2 = ST.get() in
    (**) assert(
      let ev_1 = B.deref h1 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
      let ev_2 = B.deref h2 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
      let (entr, c_r_spec) = HACLRandom.crypto_random ev_1 SpecParser.c_id_size in

      modifies2 c_r_m entropy_p h1 h2 /\  
      Ghost.reveal ev_2 == entr
      /\ Seq.equal c_r_spec (as_seq h2 c_r_m)
    );
    (**) assert(Seq.equal (as_seq hinit hs_m.msg1_hash) (as_seq h2 hs_m.msg1_hash));

    ST.pop_frame();
    CSuccess
    
    // // Compose the ephemeral shared key G_XY
    // let res_dh = dh #cs hs_m.g_xy epriv_m epub_m in
    // if (not res_dh)
    // then (
    //   /// Pop frame!!!
    //   ST.pop_frame();

    //   // if DH share composing failed
    //   CInvalidECPoint
    // )
    // else (
    //   (**) let h3 = ST.get () in
    //   (**) assert(
    //     let priv = nn_as_seq h2 epriv_m in
    //     let pub = nn_as_seq h2 epub_m in
    //     let res_spec = SpecCrypto.dh #cs priv pub in

    //     modifies1 hs_m.g_xy h2 h3 /\
    //     (Some? res_spec <==> res_dh)
    //     /\ (res_dh ==> Seq.equal (as_seq h3 hs_m.g_xy) (Some?.v res_spec))
    //   );
    //   (**) assert(Seq.equal (as_seq hinit hs_m.msg1_hash) (as_seq h3 hs_m.msg1_hash));


    //   // DH share composing succeeded
    //   // Set id_cred_r = cred_r for this implementation
    //   let id_cred_r_m = party_state_mem_get_id rs_m in
    //   let cred_r_m = party_state_mem_get_id rs_m in

    //   // compute TH2
    //   let g_y_m:ec_pub_key_buf cs = epub_m in
    //   let th2_m = hs_m.th2 in
    //   (**) assert(live h3 hs_m.msg1_hash /\ live h3 g_y_m /\ live h3 th2_m);
    //   (**) assert(B.all_disjoint [loc hs_m.msg1_hash; loc g_y_m; loc th2_m]);
    //   compute_th2_pre_hash_mem hs_m.msg1_hash g_y_m th2_m;
    //   (**) let h4 = ST.get () in
    //   (**) assert(
    //     let msg1_hash = as_seq hinit hs_m.msg1_hash in
    //     let g_y = as_seq h3 g_y_m in
    //     let th2_spec = SpecTH.compute_th2_pre_hash #cs msg1_hash g_y in

    //     modifies1 th2_m h3 h4 /\   
    //     Seq.equal th2_spec (as_seq h4 th2_m)
    //   );

    //   // derive PRK2e
    //   extract_prk2e th2_m hs_m.g_xy hs_m.prk2e;
    //   (**) let h5 = ST.get () in
    //   (**) assert(
    //     let th2 = as_seq h4 th2_m in
    //     let g_xy = as_seq h4 hs_m.g_xy in
    //     let prk2e = SpecKS.extract_prk2e #cs th2 g_xy in

    //     modifies1 hs_m.prk2e h4 h5 /\
    //     Seq.equal prk2e (as_seq h5 hs_m.prk2e)
    //   );

    //   // derive PRK3e2m
    //   let r_m = (ec_keypair_mem_get_priv (ps_mem_get_static_dh_kp rs_m)) in
    //   (**) assert(hs_mem_disjoint_to hs_m r_m); 
    //   let res_prk3e2m = derive_prk3e2m #cs auth_material hs_m.prk2e hs_m.th2 r_m hs_m.g_x hs_m.prk3e2m in
    //   (**) assert(res_prk3e2m == CSuccess \/ res_prk3e2m == CInvalidECPoint);
    //   (**) let h6 = ST.get () in
    //   (**) assert(
    //     let r = as_seq h5 r_m in
    //     let pub_r = as_seq h5 hs_m.g_x in
    //     let th2 = as_seq h5 hs_m.th2 in
    //     let prk2e = as_seq h5 hs_m.prk2e in
    //     let hs = eval_hs_mem h5 hs_m in
    //     let res_prk3e2m_spec = Spec.derive_prk3e2m #cs auth_material prk2e th2 (Some r) (Some pub_r) in

    //     (res_prk3e2m == CSuccess \/ res_prk3e2m == CInvalidECPoint)
    //     /\ (Res? res_prk3e2m_spec <==> res_prk3e2m == CSuccess)
    //     /\ (res_prk3e2m == CSuccess ==> Seq.equal (match res_prk3e2m_spec with
    //                                     Res prk3e2m -> prk3e2m) (as_seq h6 hs_m.prk3e2m)
    //                 /\ modifies1 hs_m.prk3e2m h5 h6
    //     ));



      // if (res_prk3e2m <> CSuccess)
      // then (
      //   /// Pop frame!!!
      //   ST.pop_frame();

      //   res_prk3e2m
      // )
      // else (
      //   (**) let h7 = ST.get () in
      //   (**) assert(live h7 c_r_m /\ live h7 id_cred_r_m /\ live h7 cred_r_m
      //   /\ live h7 th2_m);
      //   (**) assert(B.all_disjoint [loc c_r_m; loc id_cred_r_m; loc th2_m]);

      //   // construct context 2
      //   let ead2_m = null #MUT #uint8 in
      //   (**) assert(g_is_null ead2_m);
      //   let context2_m = construct_context2_mem #cs c_r_m id_cred_r_m th2_m cred_r_m ead2_m in
      //   (**) assert(live h7 ead2_m);
      //   (**) assert(B.all_disjoint [loc c_r_m; loc id_cred_r_m; loc th2_m; loc ead2_m]);
      //   (**) assert(is_valid_context2_mem h7 context2_m);

        // // compute MAC2
        // expand_mac2 #cs auth_material hs_m.prk3e2m context2_m mac2_m;
        // (**) let h8 = ST.get () in
        // (**) assert(
        //   let prk3e2m = as_seq h7 hs_m.prk3e2m in
        //   let c2_abstract = context2_mem_to_context2 h7 context2_m in
        //   let mac2 = SpecKS.expand_mac2 #cs auth_material prk3e2m c2_abstract in

        //   modifies1 mac2_m h7 h8
        //   /\ Seq.equal mac2 (as_seq h8 mac2_m)
        // );

        // // derive Sig_or_MAC2
        // let sk_r_m = ecdsa_sig_keypair_mem_get_priv (ps_mem_get_sig_kp rs_m) in
        // (**) let h9 = ST.get () in
        // // (**) assert(ecdsa_sig_keypair_mem_live h9 (ps_mem_get_sig_kp rs_m));
        // (**) assert(live h9 sk_r_m);
        // (**) assert(live h9 sig_or_mac2_m /\ live h9 mac2_m /\ live h9 entropy_p);
        // (**) assert(auth_material == SpecCrypto.Signature \/ auth_material == SpecCrypto.MAC);
        // (**) assert(context2_mem_disjoint_to context2_m sk_r_m
        //   /\ context2_mem_disjoint_to context2_m entropy_p
        //   /\ context2_mem_disjoint_to context2_m sig_or_mac2_m
        //   /\ context2_mem_disjoint_to context2_m mac2_m);
        // (**) assert(B.all_disjoint [loc sk_r_m; loc mac2_m; loc sig_or_mac2_m; loc entropy_p]);

        // let sig_or_mac2_res = derive_sig_or_mac2 #cs auth_material sk_r_m mac2_m
        //                 context2_m sig_or_mac2_m in
        // (**) let h10 = ST.get () in
        // (**) assert(
        //   let ev_0 = B.deref h9 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
        //   let mac2 = as_seq h8 mac2_m in
        //   assert(Seq.length mac2 = size_v (mac23_size_v cs auth_material));
        //   let ctx2 = context2_mem_to_context2 h9 context2_m in
        //   let sk_r = as_seq h9 sk_r_m in

        //   let sig_or_mac2_op = Spec.derive_sig_or_mac2 #cs auth_material ev_0 (Some sk_r)
        //                           mac2 ctx2 in

        //   (match auth_material with
        //     | SpecCrypto.Signature -> modifies2 sig_or_mac2_m entropy_p h9 h10
        //     | SpecCrypto.MAC -> modifies1 sig_or_mac2_m h9 h10)
        //   /\ (Some? sig_or_mac2_op <==> sig_or_mac2_res == CSuccess)
        //   /\ (sig_or_mac2_res == CSuccess ==> (
        //     Seq.equal (Some?.v sig_or_mac2_op) (as_seq h10 sig_or_mac2_m)
        //   )) 
        // );

        // if (sig_or_mac2_res <> CSuccess)
        // then (
        //   // Pop frame!!!
        //   ST.pop_frame();

        //   CSigningFailed
        // )
        // else (
        //   (**) let h11 = ST.get () in
        //   // construct plaintext2_mem
        //   let plaintext2_m
        //       = construct_plaintext2_mem #cs #auth_material c_r_m id_cred_r_m sig_or_mac2_m ead2_m in

        //   (**) assert(plaintext2_mem_get_length plaintext2_m = ptx2_len);
        //   // (**) assert(length ptx2_buff = size_v (plaintext2_mem_get_length plaintext2_m));
        //   // (**) assert(live h11 ptx2_buff);
        //   // (**) assert(is_valid_plaintext2_mem h11 plaintext2_m);
        //   // (**) assert(plaintext2_mem_disjoint_to_buffer plaintext2_m ptx2_buff);
        //   // serialize_ptx2_mem #cs #auth_material #ptx2_len plaintext2_m ptx2_buff;

        //   // encrypt plaintext2
        //   // encrypt_plaintext2_mem plaintext2_m th2_m hs_m.prk2e ciphertext2_m;

        //   // // // construct Message2
        //   // let message2_m = construct_message2_mem #cs #auth_material hs_m.g_y ciphertext2_m in
        //   // (**) assert(message2_mem_get_length message2_m = msg2_len);
        //   // serialize_msg2_mem message2_m msg2_buff;


        //   // Pop frame !!!
        //   ST.pop_frame();

        //   CSuccess
        // )

      //   ST.pop_frame();
      //   CSuccess
      // )

    // )

  )
#pop-options
