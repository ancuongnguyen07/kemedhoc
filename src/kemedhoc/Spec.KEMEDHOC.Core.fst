module Spec.KEMEDHOC.Core

module Seq = Lib.Sequence
module ByteSeq = Lib.ByteSequence

(*---------------------------- Common between parties*)

/// -----------------
/// Party state
/// -----------------

let init_party_state #kcs suite static_kem_kp id_cred remote_static_kem_pub_key remote_id_cred
  = {
      suite = suite;
      static_kem_kp = static_kem_kp;
      id_cred = id_cred;
      eph_kem_priv_key = None;
      remote_static_kem_pub_key = remote_static_kem_pub_key;
      remote_id_cred = remote_id_cred;
    }

/// -----------------
/// Handshake state
/// -----------------

let init_handshake_state #kcs msg1_hash th1 k_auth_R prk1e
  = {
      suite_i = Some?.v (get_kemCipherSuite_label kcs);
      msg1_hash = msg1_hash;
      k_xy = None;
      k_auth_R = k_auth_R;
      k_auth_I = None;
      th1 = th1;
      th2 = None;
      th3 = None;
      th4 = None;
      prk1e = prk1e;
      prk2e = None;
      prk3e2m = None;
      prk4e3m = None;
      prk_out = None;
      prk_exporter = None;
      remote_id_cred = None;
    }

(*------------------ Message 1*)

/// ------------------
/// Initiator sends message 1
/// ------------------

let initiator_send_msg1 kcs is entr
  = // generate connection ID C_I
  let c_i = unsound_crypto_random2 c_id_size in
  // generate ephemeral KEM keypair
  let pk_x, sk_x = kem_keygen kcs entr in
  lemma_kem_functional_correctness kcs entr;
  // encap the Responder's static public KEM key for authentication
  let ct_auth_R, k_auth_R = kem_encaps kcs entr (is.remote_static_kem_pub_key) in
  // compute TH1
  let th1 = compute_th1 #kcs pk_x ct_auth_R in
  // derive PRK1e
  let prk1e = extract_prk1e th1 k_auth_R in
  // construct plaintext1
  let cred_I = is.id_cred in
  let ptx1 = construct_ptx1 is.id_cred cred_I in
  let ptx1_byte = concat_ptx1 ptx1 in
  // encrypt plaintext1 -> ciphertext1
  let c1 = encrypt_plaintext1 ptx1 th1 prk1e in
  // construct message1
  let msg1 = {
    method = KemKem;
    suite_i = Some?.v (get_kemCipherSuite_label kcs);
    pk_x = pk_x;
    ct_auth_R = ct_auth_R;
    c_i = c_i;
    c1 = c1;
  } in
  // compute hash of message1
  let msg1_hash = do_hash kcs (concat_msg1 msg1) in
  // construct handshake state
  let hs = init_handshake_state #kcs msg1_hash th1 k_auth_R prk1e in
  // return
  Res (msg1, {is with eph_kem_priv_key = Some sk_x}, hs)

/// ------------------
/// Responder processes message 1
/// ------------------

let responder_process_msg1 kcs rs msg1
  = // decap ct_auth_R -> get K_auth_R
  let sk_R = get_priv_kem_key rs.static_kem_kp in
  let k_auth_R = kem_decaps kcs msg1.ct_auth_R sk_R in
  // derive TH1
  let th1 = compute_th1 #kcs msg1.pk_x msg1.ct_auth_R in
  // derive PRk1e
  let prk1e = extract_prk1e th1 k_auth_R in
  // decrypt ciphertext1
  match (decrypt_ciphertext1 #kcs msg1.c1 th1 prk1e) with
    | None -> Fail DecryptionFailed
    | Some ptx1_byte -> (
      // compute hash of message 1
      let msg1_hash = do_hash kcs (concat_msg1 msg1) in
      // construct handshake state
      let hs = init_handshake_state #kcs msg1_hash th1 k_auth_R prk1e in
      let ptx1 = deserialize_ptx1 ptx1_byte in

      // check if the credential matches any remote credential
      // stored locally in the Responder. In this case,
      // only one credential is supported. In real-world applications,
      // this should be a list of credentials.
      if (not (ByteSeq.lbytes_eq ptx1.id_cred_I rs.remote_id_cred))
        then Fail InvalidCredential
        else Res ({hs with remote_id_cred = Some ptx1.id_cred_I}, ptx1)
    )

let bundle_msg1 (kcs: supportedKemCipherSuite)
  (is: party_state #kcs) (rs: party_state #kcs) (entr: entropy)
  : eresult (message1 #kcs & handshake_state_init #kcs & handshake_state_init #kcs
            & party_state_eph_est #kcs & party_state #kcs & plaintext1)
  = match (initiator_send_msg1 kcs is entr) with
      | Res (msg1, is', hs_i) -> (
          match (responder_process_msg1 kcs rs msg1) with
            | Fail e -> Fail e
            | Res (hs_r, ptx1) -> (
                Res (msg1, hs_i, hs_r, is', rs, ptx1)
            )
        )

(*------------------ Message 2*)

/// Responder sends message 2
let responder_send_msg2 kcs rs hs msg1 entr
  = // encaps pk_x -> ct_y, k_xy
  let ct_y, k_xy = kem_encaps kcs entr msg1.pk_x in
  // encaps pk_I -> ct_auth_I, k_auth_I
  let pk_I = rs.remote_static_kem_pub_key in
  let ct_auth_I, k_auth_I = kem_encaps kcs entr pk_I in
  // derive TH2
  let th2 = compute_th2 ct_y k_auth_I msg1 in
  // derive PRK2e
  let prk2e = extract_prk2e hs.prk1e th2 k_xy in
  // derive SALT3e2m
  let salt3e2m = expand_salt3e2m prk2e th2 in
  // derive PRK3e2m
  let prk3e2m = extract_prk3e2m salt3e2m hs.k_auth_R in

  // randomly generate connection ID C_R
  let c_R = unsound_crypto_random2 c_id_size in
  // construct context2
  let id_cred_R = rs.id_cred in
  let cred_R = id_cred_R in
  let ctx2 = construct_context2 c_R id_cred_R th2 cred_R in
  // derive MAC2
  let mac2 = expand_mac2 prk3e2m ctx2 in
  // construct plaintext2
  let ptx2 = construct_ptx2 c_R id_cred_R cred_R mac2 in
  // encrypt plaintext2 -> ciphertext2
  let c2 = encrypt_plaintext2 ptx2 th2 prk2e in
  // construct message 2
  let msg2 = concstruct_msg2 ct_y ct_auth_I c2 in

  Res (msg2, { hs with 
    k_xy = Some k_xy;
    k_auth_I = Some k_auth_I;
    th2 = Some th2;
    prk2e = Some prk2e;
    prk3e2m = Some prk3e2m;
  })


/// Initiator processes message 2

let initiator_process_msg2 kcs is hs msg2
  = // decap ct_y -> k_xy
  let sk_X = Some?.v is.eph_kem_priv_key in
  let k_xy = kem_decaps kcs msg2.ct_y sk_X in
  // decap ct_auth_I -> k_auth_I
  let sk_I = get_priv_kem_key is.static_kem_kp in
  let k_auth_I = kem_decaps kcs msg2.ct_auth_I sk_I in
  // derive TH2
  let th2 = compute_th2_pre_hash msg2.ct_y k_auth_I hs.msg1_hash in
  // derive PRK2e
  let prk2e = extract_prk2e hs.prk1e th2 k_xy in
  // decrypt ciphertext2
  match (decrypt_ciphertext2 msg2.c2 th2 prk2e) with
    | None -> Fail DecryptionFailed
    | Some ptx2_byte -> (
      // derive SALT3e2m
      let salt3e2m = expand_salt3e2m prk2e th2 in
      // derive PRK3e2m
      let prk3e2m = extract_prk3e2m salt3e2m hs.k_auth_R in
      // construct ptx2
      let ptx2 = deserialize_ptx2 ptx2_byte in

      // check if the credential matches any remote credential
      // stored locally in the Initiator. In this case,
      // only one credential is supported. In real-world applications,
      // this should be a list of credentials.
      if (not (ByteSeq.lbytes_eq ptx2.id_cred_R is.remote_id_cred))
        then Fail InvalidCredential
        else (
          // construct context2
          let ctx2 = construct_context2 ptx2.c_R ptx2.id_cred_R th2 ptx2.cred_R in
          // derive MAC2
          let mac2 = expand_mac2 prk3e2m ctx2 in
          // check MAC2
          if (not (ByteSeq.lbytes_eq ptx2.mac2 mac2))
            then Fail IntegrityCheckFailed
            else (
              // construct handshake state
              let hs' = {
                hs with
                k_xy = Some k_xy;
                k_auth_I = Some k_auth_I;
                th2 = Some th2;
                prk2e = Some prk2e;
                prk3e2m = Some prk3e2m;
              } in
              Res (hs', ptx2)
            )
        )
    )


/// Bundle message 1 and message 2

let bundle_msg1_msg2 (kcs: supportedKemCipherSuite)
  (is: party_state #kcs) (rs: party_state #kcs) (entr: entropy)
  : eresult (message2 #kcs & handshake_state_after_msg2 #kcs & handshake_state_after_msg2 #kcs
            & party_state_eph_est #kcs & party_state #kcs & plaintext2 #kcs)
  = match (bundle_msg1 kcs is rs entr) with
    | Fail e -> Fail e
    | Res (msg1, hs_i', hs_r', is', rs, ptx1) -> (
      match (responder_send_msg2 kcs rs hs_r' msg1 entr) with
        | Res (msg2, hs_r'') -> (
          match (initiator_process_msg2 kcs is' hs_i' msg2) with
            | Fail e -> Fail e
            | Res (hs_i'', ptx2) -> (
              Res (msg2, hs_i'', hs_r'', is', rs, ptx2)
            )
        )
    )


(*------------------ Message 3*)

/// Initiator sends message 3
let initiator_send_msg3 kcs is hs ptx2 msg2
  = // derive TH3
  let th2 = Some?.v hs.th2 in
  let th3 = compute_th3 th2 ptx2 ptx2.id_cred_R in
  // construct context3
  let cred_I = is.id_cred in
  let ctx3 = construct_context3 is.id_cred th3 cred_I in
  // derive salt4e3m
  let prk3e2m = Some?.v hs.prk3e2m in
  let salt4e3m = expand_salt4e3m prk3e2m th3 in
  // derive prk4e3m
  let k_auth_I = Some?.v hs.k_auth_I in
  let prk4e3m = extract_prk4e3m salt4e3m k_auth_I in
  // derive MAC3
  let mac3 = expand_mac3 prk4e3m ctx3 in
  // construct plaintext3
  let ptx3 = construct_ptx3 is.id_cred mac3 in
  // encrypt plaintext3 -> ciphertext3
  // message3 is just a ciphertext3
  let c3 = encrypt_plaintext3 ptx3 th3 prk3e2m in

  // compute th4
  let th4 = compute_th4 th3 ptx3 cred_I in
  // derive prk_out
  let prk_out = expand_prk_out prk4e3m th4 in
  // derive prk_exporter
  let prk_exporter = expand_prk_exporter prk_out in

  Res (c3, {hs with
    th3 = Some th3;
    prk4e3m = Some prk4e3m;
    prk_out = Some prk_out;
    prk_exporter = Some prk_exporter
  })

/// Responder processes message 3
let responder_process_msg3 kcs rs hs ptx2 msg3
  = // derive TH3
  let th2 = Some?.v hs.th2 in
  let cred_R = rs.id_cred in
  let th3 = compute_th3 th2 ptx2 cred_R in
  // derive salt4e3m
  let prk3e2m = Some?.v hs.prk3e2m in
  // decrypt message3 (ciphertext3) -> plaintext3
  match (decrypt_ciphertext3 msg3 th3 prk3e2m) with
    | None -> Fail DecryptionFailed
    | Some ptx3_byte -> (
      let ptx3 = deserialize_ptx3 ptx3_byte in

      // derive salt4e3m
      let prk3e2m = Some?.v hs.prk3e2m in
      let salt4e3m = expand_salt4e3m prk3e2m th3 in
      // derive prk4e3m
      let k_auth_I = Some?.v hs.k_auth_I in
      let prk4e3m = extract_prk4e3m salt4e3m k_auth_I in
      // construct context3
      let id_cred_I = ptx3.id_cred_I in
      let cred_I = id_cred_I in

      // check if the id_cred_I is equal to the one received
      // in msg1. TODO!

      let ctx3 = construct_context3 id_cred_I th3 cred_I in
      // derive MAC3
      let mac3 = expand_mac3 prk4e3m ctx3 in

      // check MAC3
      if (not (ByteSeq.lbytes_eq ptx3.mac3 mac3))
        then Fail IntegrityCheckFailed
        else (
          // compute th4
          let th4 = compute_th4 th3 ptx3 cred_I in
          // derive prk_out
          let prk_out = expand_prk_out prk4e3m th4 in
          // derive prk_exporter
          let prk_exporter = expand_prk_exporter prk_out in

          // construct handshake state after message 3
          Res ({hs with
            th3 = Some th3;
            prk4e3m = Some prk4e3m;
            prk_out = Some prk_out;
            prk_exporter = Some prk_exporter
          }, ptx3)
        )
    )

/// Bundle message 3

let bundle_msg1_msg2_msg3 (kcs: supportedKemCipherSuite)
  (is: party_state #kcs) (rs: party_state #kcs) (entr: entropy)
  : eresult (message3 kcs & handshake_state_after_msg3 #kcs &
    handshake_state_after_msg3 #kcs & party_state_eph_est #kcs &
    party_state #kcs & plaintext3 #kcs)
  = match (bundle_msg1_msg2 kcs is rs entr) with
    | Fail e -> Fail e
    | Res (msg2, hs_i'', hs_r'', is', rs, ptx2) -> (
      match (initiator_send_msg3 kcs is' hs_i'' ptx2 msg2) with
        | Res (c3, hs_i''') -> (
          match (responder_process_msg3 kcs rs hs_r'' ptx2 c3) with
            | Fail e -> Fail e
            | Res (hs_r''', ptx3) -> (
              Res (c3, hs_i''', hs_r''', is', rs, ptx3)
            )
        )
    )
