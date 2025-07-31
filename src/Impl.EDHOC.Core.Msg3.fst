module Impl.EDHOC.Core.Msg3

open Lib.RawIntTypes
open Lib.ByteBuffer

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence


// friend Spec.EDHOC.Core
// friend Spec.EDHOC.Core.Lemmas

module Spec = Spec.EDHOC.Core
module SpecParser = Spec.EDHOC.Parser
module SpecDef = Spec.EDHOC.Base.Definitions
module SpecKS = Spec.EDHOC.KeySchedule
module SpecTH = Spec.EDHOC.TranscriptHash
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecEncDec = Spec.EDHOC.Ciphertext


(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)
let responder_process_msg3 #cs #msg3_len method rs_m hs_m ptx2_m msg3_m
  = let hinit = ST.get () in
  /// get authentication materials
  let i_auth_material = SpecCrypto.get_auth_material Initiator method in
  let r_auth_material = SpecCrypto.get_auth_material Responder method in

  let aead_tag_size_v = size (SpecCrypto.aead_tag_size (SpecCrypto.get_aead_alg cs)) in

  /// Push frame!!!
  ST.push_frame();

  /// Allocation: plaintext3
  let ptx3_len = plaintext3_len_fixed_v cs i_auth_material in
  let ptx3_buff = create ptx3_len (u8 0) in
  (**) assert(SpecParser.is_valid_ptx3_size cs i_auth_material (size_v ptx3_len));
  // (**) assert(hs_mem_disjoint_to hs_m ptx3_buff);

  let c3_len = ptx3_len +! aead_tag_size_v in
  (**) assert(length msg3_m = size_v c3_len);

  /// Allocation: id_cred_i, sig_or_mac3, ead3
  let id_cred_i_m = create (size SpecParser.id_cred_size) (u8 0) in
  let sig_or_mac3_m = create (sig_or_mac23_size_v cs i_auth_material) (u8 0) in
  let ead3_m = null #MUT #uint8 in

  /// Allocation: MAC3
  let mac3_len = mac23_size_v cs i_auth_material in
  let mac3_m = create mac3_len (u8 0) in

  let id_cred_r_m = ps_mem_get_id_cred rs_m in
  let cred_r_m = ps_mem_get_id_cred rs_m in

  // Compute TH3
  compute_th3_mem r_auth_material hs_m.th2 ptx2_m cred_r_m hs_m.th3;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 hs_m.th3 hinit h1);
  (**) assert(is_legit_hs_mem h1 hs_m);

  // decrypt msg3, aka ciphertext3
  let c3_m = msg3_m in
  // (**) assert(length c3_m = length ptx3_buff +! aead_tag_size_v)
  let res_c3_m = decrypt_ciphertext3 #cs #i_auth_material #c3_len c3_m hs_m.th3 hs_m.prk3e2m ptx3_buff in
  (**) let h2 = ST.get () in
  (**) assert(res_c3_m == CSuccess ==> modifies1 ptx3_buff h1 h2);
  // (**) assert(is_legit_hs_mem h2 hs_m);

  // ST.pop_frame();
  // CSuccess

  if (res_c3_m <> CSuccess)
  then (
    ST.pop_frame();

    CDecryptionFailure
  )
  else (
    (**) let h2 = ST.get () in
    // (**) assert(res_c3_m == CSuccess);
    // (**) assert(modifies1 ptx3_buff h1 h2);
    // (**) assert(hs_mem_disjoint_to hs_m ptx3_buff);
    // (**) assert(is_legit_hs_mem h2 hs_m);

    // deserialize plaintext3
    deserialize_ptx3_mem #cs #i_auth_material #ptx3_len #(size SpecParser.id_cred_size)
                        #(sig_or_mac23_size_v cs i_auth_material)
                        ptx3_buff id_cred_i_m sig_or_mac3_m ead3_m;
    (**) let h3 = ST.get () in
    (**) assert(modifies2 id_cred_i_m sig_or_mac3_m h2 h3);
    // (**) assert(is_legit_hs_mem h3 hs_m);


    let cred_i_m = id_cred_i_m in

    // construct plaintext3 struct
    let ptx3_m
      = construct_plaintext3_mem #cs #i_auth_material id_cred_i_m sig_or_mac3_m ead3_m in

    // construct context3 struct
    let context3_m = construct_context3_mem #cs id_cred_i_m hs_m.th3 cred_i_m ead3_m in
    (**) let h4 = ST.get () in
    (**) assert(is_valid_plaintext3_mem h4 ptx3_m);
    (**) assert(is_valid_context3_mem h4 context3_m);
    // (**) assert(is_legit_hs_mem h4 hs_m);

    // derive PRK4e3m
    let y_m = opt_ec_keypair_mem_get_priv (ps_mem_get_eph_keypair rs_m) in
    let g_i_m = ps_mem_get_remote_static_pub rs_m in
    (**) assert(hs_mem_disjoint_to hs_m y_m);
    (**) assert(hs_mem_disjoint_to hs_m g_i_m);
    (**) assert(~(g_is_null y_m));
    let res_prk4e3m
      = derive_prk4e3m #cs i_auth_material hs_m.prk3e2m hs_m.th3 y_m g_i_m hs_m.prk4e3m in
    // (**) let h5 = ST.get () in
    // (**) assert(res_prk4e3m == CSuccess ==> modifies1 hs_m.prk4e3m h4 h5);

  //   if (res_prk4e3m <> CSuccess)
  //   then (
  //     ST.pop_frame();

  //     CInvalidECPoint
  //   )
  //   else (

  //     // compute MAC3
  //     expand_mac3 #cs i_auth_material hs_m.prk4e3m context3_m mac3_m;
  //     (**) let h6 = ST.get () in
  //     (**) assert(modifies1 mac3_m h5 h6);

  //     // verify Sig_or_MAC3
  //     let pk_i_m = ps_mem_get_remote_sig_pub rs_m in
  //     let is_valid_sig_or_mac3
  //       = verify_sig_or_mac3 i_auth_material sig_or_mac3_m mac3_m context3_m pk_i_m in

  //     if (not is_valid_sig_or_mac3)
  //     then (
  //       ST.pop_frame();

  //       CIntegrityCheckFailed
  //     )
  //     else (
  //       /// Check if the Responder's credential is identical to the Initiator's credential
  //       /// this prevents against Reflection Attack, aka Selfie Attack
  //       if (lbytes_eq cred_i_m cred_r_m)
  //       then (
  //         ST.pop_frame();

  //         CInvalidCredential
  //       )
  //       else (
  //         // And check if the received credential in the local list of Responder
  //         if (not (lbytes_eq cred_i_m (ps_mem_get_remote_id_cred rs_m)))
  //         then (
  //           ST.pop_frame();

  //           CUnknownCredentialID
  //         )
  //         else (
  //           // compute TH4
  //           compute_th4_mem #cs i_auth_material hs_m.th3 ptx3_m cred_i_m hs_m.th4;
  //           (**) let h7 = ST.get () in
  //           (**) assert(modifies1 hs_m.th4 h6 h7);

  //           // derive PRK_OUT
  //           expand_prk_out #cs hs_m.prk4e3m hs_m.th4 hs_m.prk_out;
  //           (**) let h8 = ST.get () in
  //           (**) assert(modifies1 hs_m.prk_out h7 h8);

  //           // derive PRK_Exporter
  //           expand_prk_exporter #cs hs_m.prk_out hs_m.prk_exporter;
  //           (**) let h9 = ST.get () in
  //           (**) assert(modifies1 hs_m.prk_exporter h8 h9);

            ST.pop_frame();

            CSuccess

  //         )

  //       )
  //     )

  //   )

  )


(*-------------------------------------------*)
(*---------------------------- Initiator side*)
(*-------------------------------------------*)
#push-options "--z3rlimit 30 --max_fuel 4"
let initiator_send_msg3 #cs #msg3_len method is_m hs_m ptx2_m msg3_buff
  = let hinit = ST.get () in
  /// get authentication materials
  let i_auth_material = SpecCrypto.get_auth_material Initiator method in
  let r_auth_material = SpecCrypto.get_auth_material Responder method in

  let aead_tag_size_v = size (SpecCrypto.aead_tag_size (SpecCrypto.get_aead_alg cs)) in

  /// Push frame!!!
  ST.push_frame();

  /// All allocation should be done at the beginning HERE!
  /// Allocation: MAC3
  let mac3_len = mac23_size_v cs i_auth_material in
  let mac3_m = create mac3_len (u8 0) in
  let ead3_m = null #MUT #uint8 in

  /// Allocation: Sig_or_MAC3
  let sig_or_mac3_m = create (sig_or_mac23_size_v cs i_auth_material) (u8 0) in
  (**) assert(disjoint mac3_m sig_or_mac3_m);

  /// Allocation: Plaintext3
  let ptx3_len = plaintext3_len_fixed_v cs i_auth_material in
  let ptx3_buff = create ptx3_len (u8 0) in

  /// Message 3 is also the Ciphertext3
  let c3_m = msg3_buff in

  let cred_r_m = plaintext2_mem_get_id_cred_r ptx2_m in
  let g_y_m = hs_m.g_y in

  let id_cred_i_m = ps_mem_get_id_cred is_m in
  let cred_i_m = ps_mem_get_id_cred is_m in

  // compute TH3
  compute_th3_mem r_auth_material hs_m.th2 ptx2_m cred_r_m hs_m.th3;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 hs_m.th3 hinit h1);

  // derive PRK4e3m
  let i_m = ec_keypair_mem_get_priv (ps_mem_get_static_dh_kp is_m) in
  let res_prk4e3m
    = derive_prk4e3m #cs i_auth_material hs_m.prk3e2m hs_m.th3 i_m g_y_m hs_m.prk4e3m in
  (**) let h2 = ST.get () in
  (**) assert(res_prk4e3m == CSuccess ==> modifies1 hs_m.prk4e3m h1 h2);

  if (res_prk4e3m <> CSuccess)
  then (
    ST.pop_frame();

    CInvalidECPoint
  )
  else (
    (**) assert(res_prk4e3m == CSuccess);

    // construct Context3
    let context3_m = construct_context3_mem id_cred_i_m hs_m.th3 cred_i_m ead3_m in
    (**) let h3 = ST.get () in
    (**) assert(is_valid_context3_mem h3 context3_m);
    
    // compute MAC3
    expand_mac3 #cs i_auth_material hs_m.prk4e3m context3_m mac3_m;
    (**) let h4 = ST.get () in
    (**) assert(modifies1 mac3_m h3 h4);

    // derive Sig_or_MAC3
    let sk_i_m = ecdsa_sig_keypair_mem_get_priv (ps_mem_get_sig_kp is_m) in
    (**) assert(B.all_disjoint [loc sk_i_m; loc mac3_m; loc sig_or_mac3_m; loc entropy_p]);
    let res_sig_or_mac3 = derive_sig_or_mac3 #cs i_auth_material sk_i_m mac3_m context3_m sig_or_mac3_m in
    (**) let h5 = ST.get () in
    (**) assert(
      match i_auth_material with
        | SpecCrypto.Signature -> modifies2 sig_or_mac3_m entropy_p h4 h5
        | SpecCrypto.MAC -> modifies1 sig_or_mac3_m h4 h5
    );
    (**) assert(is_legit_hs_mem h5 hs_m);

    if (res_sig_or_mac3 <> CSuccess)
    then (
      ST.pop_frame();

      CInvalidECPoint
    )
    else (
      (**) assert(res_sig_or_mac3 == CSuccess);

      // construct plaintext3
      let ptx3_m
        = construct_plaintext3_mem #cs #i_auth_material id_cred_i_m sig_or_mac3_m ead3_m in
      (**) let h5 = ST.get () in
      (**) assert(is_valid_plaintext3_mem h5 ptx3_m);
      (**) assert(plaintext3_mem_get_length ptx3_m = ptx3_len);

      // encrypt plaintext3
      // Note that the resulting ciphertext3 is also the message 3
      let res_c3 = encrypt_plaintext3 #cs #i_auth_material ptx3_len ptx3_m hs_m.th3 hs_m.prk3e2m msg3_buff in
      (**) let h6 = ST.get () in
      (**) assert(res_c3 == CSuccess \/ res_c3 == CUnsupportedAlgorithmOrInvalidConfig);
      (**) assert(
        match res_c3 with
          | CSuccess -> modifies1 msg3_buff h5 h6
          | CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h5 h6
      );
      (**) assert(is_legit_hs_mem h6 hs_m);

      if (res_c3 <> CSuccess)
      then (
        ST.pop_frame();

        CUnsupportedAlgorithmOrInvalidConfig
      )
      else (
        (**) assert(res_c3 == CSuccess);

        // compute TH4
        compute_th4_mem #cs i_auth_material hs_m.th3 ptx3_m cred_i_m hs_m.th4;
        (**) let h7 = ST.get () in
        (**) assert(modifies1 hs_m.th4 h6 h7);

        // derive PRK_OUT
        expand_prk_out #cs hs_m.prk4e3m hs_m.th4 hs_m.prk_out;
        (**) let h8 = ST.get () in
        (**) assert(modifies1 hs_m.prk_out h7 h8);

        // derive PRK_Exporter
        expand_prk_exporter #cs hs_m.prk_out hs_m.prk_exporter;
        (**) let h9 = ST.get () in
        (**) assert(modifies1 hs_m.prk_exporter h8 h9);

        (**) assert(is_legit_hs_mem h9 hs_m);

        // Now the resulting message3 is the computed ciphertext3 above
        // No need to do copy as `msg3_buff` was refered into ciphertext3 computation
        // as shown above.

        ST.pop_frame();
        CSuccess
      )

      // ST.pop_frame();

      // CSuccess
    )
  )


#pop-options
