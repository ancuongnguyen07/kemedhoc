module Spec.EDHOC.Core

// open FStar.Mul
// open FStar.List.Tot

// open Spec.EDHOC.Base.Definitions
// open Spec.EDHOC.CommonPred
// open Spec.EDHOC.Serialization
// // open Spec.EDHOC.CryptoPrimitives
// open Spec.EDHOC.TranscriptHash
// open Spec.EDHOC.Ciphertext
// open Spec.EDHOC.KeySchedule

// (*HACL libs*)
// open Lib.IntTypes
// open Lib.RawIntTypes
// open Lib.ByteSequence
// open Lib.Sequence

// friend Spec.EDHOC.Parser
// friend Spec.EDHOC.Ciphertext

module HACLRandom = Lib.RandomSequence

(*---------------------------- Utilities*)

(*---------------------------- Common between parties*)
let init_party_state suites static_dh signature_key id_cred
    remote_static_pub_key remote_signature_pub_key remote_id_cred
  = {
    suites = suites;
    static_dh = static_dh;
    signature_key = signature_key;
    id_cred = id_cred;
    eph_ec_keypair = None;
    remote_static_pub_key = remote_static_pub_key;
    remote_signature_pub_key = remote_signature_pub_key;
    remote_id_cred = remote_id_cred;
  }

let init_handshake_state cs method g_x msg1_hash
  = 
  let suite_i = get_supportedCipherSuite_label cs in
  let hs: handshake_state #cs = {
    suite_i = suite_i;
    method = method;
    g_x = g_x;
    msg1_hash = msg1_hash;
    // the below fields are set as None attentonally
    // at the initial stage.
    g_y = None;
    // msg1 = None;
    // msg2 = None;
    g_xy = None;
    g_rx = None;
    g_iy = None;
    th2 = None;
    th3 = None;
    th4 = None;
    prk2e = None;
    prk3e2m = None;
    prk4e3m = None;
    prk_out = None;
    prk_exporter = None;
  } in
  hs

let party_set_up cipherSuite_list method
  = {
    suites = cipherSuite_list;
    method = method;
  }

/// Intermediate-private function: derive PRK3e2m
let derive_prk3e2m (#cs:supported_cipherSuite)
  (auth_material:authentication_material)
  (prk2e:hash_out cs) (th2:hash_out cs)
  (r:option (ec_priv_key cs)
  {(auth_material == MAC) ==> Some? r})
  (pub_r:option (ec_pub_key cs){
    (auth_material == MAC) ==> Some? pub_r
  })
  :eresult (hash_out cs)
  = match auth_material with
      | Signature -> Res prk2e
      | MAC -> (
        match (dh (Some?.v r) (Some?.v pub_r)) with
          | None -> Fail InvalidECPoint
          | Some shared_secret -> (
            // derive SALT3e2m
            let salt3e2m = expand_salt3e2m prk2e th2 in
            Res (extract_prk3e2m salt3e2m shared_secret)
          )
      )

/// Intermediate-private function: derive PRK4e3m
let derive_prk4e3m (#cs:supported_cipherSuite)
  (auth_material:authentication_material)
  (prk3e2m:hash_out cs) (th3:hash_out cs)
  (i:option (ec_priv_key cs)
  {(auth_material == MAC) ==> Some? i})
  (pub_i:option (ec_pub_key cs){
    (auth_material == MAC) ==> Some? pub_i
  })
  :eresult (hash_out cs)
  = match auth_material with
    | Signature -> Res prk3e2m
    | MAC -> (
      match (dh (Some?.v i) (Some?.v pub_i)) with
        | None -> Fail InvalidECPoint
        | Some shared_secret -> (
          // derive SALT4e3m
          let salt4e3m = expand_salt4e3m prk3e2m th3 in
          Res (extract_prk4e3m salt4e3m shared_secret)
        )
    )

(*-------------------------------------------*)
(*---------------------------- Initiator side*)
(*-------------------------------------------*)

/// Verify Sig_or_MAC2
let verify_sig_or_mac2 (#cs:supported_cipherSuite)
  (auth_material:authentication_material)
  (sig_or_mac2:lbytes (sig_or_mac23_size cs auth_material))
  (mac2:lbytes (mac23_size cs auth_material))
  (c2:context2 #cs)
  (pk_r:option (ec_signature_pub_key cs){
    auth_material == Signature ==> Some? pk_r
  })
  : bool
  = let ead2_op = c2.ead2 in
  let id_cred_r = c2.id_cred_r in
  let cred_r = c2.cred_r in
  let th2 = c2.th2 in
  
  match auth_material with
      | Signature -> (
        assert(length sig_or_mac2 = signature_size);
        let to_be_verified = match ead2_op with
            | None -> id_cred_r @< th2 @< cred_r @< mac2
            | Some ead2 -> (
              let ead2_lbytes:lbytes (length ead2) = ead2 in
              id_cred_r @< th2 @< cred_r @< ead2_lbytes @< mac2
            )
            in
        // let pk_r = is.remote_signature_pub_key in
        ecdsa_verify to_be_verified (Some?.v pk_r) sig_or_mac2
      )
      | MAC -> (
        assert(length sig_or_mac2 = mac23_size cs auth_material);
        lbytes_eq mac2 sig_or_mac2
      )
      
/// Derive Sig_or_MAC3
let derive_sig_or_mac3 (#cs:supported_cipherSuite)
  (auth_material:authentication_material)
  (entr: HACLRandom.entropy)
  (sk_i_op:option (ec_signature_priv_key cs){
    auth_material == Signature ==> Some? sk_i_op
  })
  (mac3:lbytes (mac23_size cs auth_material))
  (c3:context3 #cs)
  : option (sig_or_mac23_bytes cs auth_material)
  = let ead3_op = c3.ead3 in
  let id_cred_i = c3.id_cred_i in
  let cred_i = c3.cred_i in
  let th3 = c3.th3 in
  
  match auth_material with
      | MAC -> Some mac3
      | Signature -> (
        let to_be_signed = match ead3_op with
            | None -> id_cred_i @< th3 @< cred_i @< mac3
            | Some ead3 -> (
              let ead3_lbytes:lbytes (length ead3) = ead3 in
              id_cred_i @< th3 @< cred_i @< ead3_lbytes @< mac3
            )
            in
        
        // let sk_i = is.signature_key.priv in
        let sk_i = Some?.v sk_i_op in
        let (entr3, nonce) = HACLRandom.crypto_random entr nonceP256_size in
        ecdsa_sign (Some nonce) to_be_signed sk_i
      )

/// Handshake's state `hs` at this point should contains
/// the cipher suite chosen by I `suite_i` and authentication method `method`
let initiator_send_msg1 cs method entr is
  = let eph_ec_keypair = generate_ec_keypair cs entr in
    match eph_ec_keypair with
      | None -> Fail InvalidECPoint
      | Some (x_gx, entr1) -> (
        let x = x_gx.priv in
        let g_x = x_gx.pub in
        // assert ((Some?.v (secret_to_public x)) == g_x);

        let (entr2, c_i_random) = HACLRandom.crypto_random entr1 c_id_size in
        let suite_i = get_supportedCipherSuite_label cs in
        let msg1: message1 = {
          method = method;
          suite_i = suite_i;
          g_x = x_gx.pub;
          c_i = c_i_random;
          // Temporarily does not use EAD1 here
          // Test vectors from the reference implementation neither have EAD1 values
          ead1 = None;
        } in

        let hash_msg1 = do_hash cs (concat_msg1 msg1) in
        let hs:handshake_state #cs = init_handshake_state cs method g_x hash_msg1 in

        let updated_is = {is with eph_ec_keypair = Some x_gx} in
        // let updated_hs = {hs with msg1 = Some msg1} in

        // assert (msg1.method = method);
        // assert (updated_hs.method = method);

        Res (msg1, updated_is, hs)
      )

let initiator_process_msg2 #cs is hs msg2
  = let auth_method = hs.method in
    let auth_material = get_auth_material Initiator auth_method in
    let remote_auth_material = get_auth_material Responder auth_method in
    // At this point it is guaranteed that authentication method
    // and authentication material are matched
    let g_y = msg2.g_y in
    let x = (Some?.v is.eph_ec_keypair).priv in
    match (dh x g_y) with
      | None -> Fail InvalidECPoint
      | Some g_xy -> (
        let id_cred_i:lbytes (length is.id_cred) = is.id_cred in
        let cred_i:lbytes (length is.id_cred) = is.id_cred in
        // compute TH2
        // let th2 = compute_th2 (Some?.v hs.msg1) g_y in
        let th2 = compute_th2_pre_hash #cs hs.msg1_hash g_y in
        // derive PRK2e
        let prk2e = extract_prk2e th2 g_xy in
        // decrypt ciphertext2
        let ciphertext2 = msg2.ciphertext2 in
        let serialized_ptx2 = decrypt_ciphertext2 #cs #remote_auth_material ciphertext2 th2 prk2e in
        let serialized_ptx2_len = length serialized_ptx2 in
        assert(serialized_ptx2_len <= okm_len_max_size
              /\ serialized_ptx2_len >= min_ptx2_size cs remote_auth_material);

            // deserialize plaintext2 to component raw bytes
            let (c_r, id_cred_r, sig_or_mac2_raw, ead2_op)
              = deserialize_ptx2_raw_bytes cs remote_auth_material serialized_ptx2 in
                // Does not support EAD2 now
                let id_cred_r:lbytes (length id_cred_r) = id_cred_r in
                // let cred_r is id_cred_r in this implementation
                let cred_r = id_cred_r in

                // convert sig_or_mac2 raw bytes to type sig_or_mac23_bytes
                // let sig_or_mac2_op = bytes_to_sig_or_mac23_bytes cs remote_auth_material sig_or_mac2_raw in
                let sig_or_mac2 = sig_or_mac2_raw in
                    // construct `plaintext2` record from component raw bytes
                    let ptx2 = construct_ptx2 c_r id_cred_r sig_or_mac2 ead2_op in
                    // get the `id_cred_r` the Initiator should verify Responder certificate here
                    // but this model leave it for application operating upon EDHOC protocol.

                    // derive PRK3e2m
                    let prk3e2m_res:eresult (hash_out cs)
                      = derive_prk3e2m #cs remote_auth_material prk2e th2
                        (Some (Some?.v is.eph_ec_keypair).priv) (Some is.remote_static_pub_key) in
                      // = match remote_auth_material with
                      //     | Signature -> Res prk2e
                      //     | MAC-> (
                      //       // get ephemeral-static DH share for implicit authentication
                      //       let g_r = is.remote_static_pub_key in
                      //       let x = (Some?.v is.eph_ec_keypair).priv in
                      //       match (dh x g_r) with
                      //         | None -> Fail InvalidECPoint
                      //         | Some g_rx -> (
                      //           // derive SALT3e2m
                      //           // let g_rx = Some?.v ephe_stat_shared in
                      //           let salt3e2m = expand_salt3e2m prk2e th2 in
                      //           Res (extract_prk3e2m salt3e2m g_rx)
                      //         )
                      //     )
                      //     in

                    match prk3e2m_res with
                      | Fail _ -> Fail InvalidECPoint
                      | Res prk3e2m -> (
                        // construct context2
                        let ctx2 = construct_context2 c_r cred_r th2 cred_r ead2_op in

                        // verify sig_or_mac2
                        // compute mac2
                        let mac2 = expand_mac2 #cs remote_auth_material prk3e2m ctx2 in
                        // let is_valid_sig_or_mac2 = match sig_or_mac2 with
                        //   | Inl signature -> (
                        //     let to_be_verified = match ead2_op with
                        //                           | None -> id_cred_r @< th2 @< cred_r @< mac2
                        //                           | Some ead2 -> id_cred_r @< th2 @< cred_r @< ead2 @< mac2
                        //                           in
                        //     let pk_r = is.remote_signature_pub_key in
                        //     ecdsa_verify to_be_verified pk_r signature
                        //   )
                        //   | Inr rev_mac2 -> (
                        //     lbytes_eq mac2 rev_mac2
                        //   )
                        //   in
                        let pk_r = is.remote_signature_pub_key in
                        let is_valid_sig_or_mac2 = verify_sig_or_mac2 #cs remote_auth_material
                                                      sig_or_mac2 mac2 ctx2 (Some pk_r) in
                          // match remote_auth_material with
                          // | Signature -> (
                          //   assert(length sig_or_mac2 = signature_size);
                          //   let to_be_verified = match ead2_op with
                          //       | None -> id_cred_r @< th2 @< cred_r @< mac2
                          //       | Some ead2 -> (
                          //         let ead2_lbytes:lbytes (length ead2) = ead2 in
                          //         id_cred_r @< th2 @< cred_r @< ead2_lbytes @< mac2
                          //       )
                          //       in
                          //   let pk_r = is.remote_signature_pub_key in
                          //   ecdsa_verify to_be_verified pk_r sig_or_mac2
                          // )
                          // | MAC -> (
                          //   assert(length sig_or_mac2 = mac23_size cs remote_auth_material);
                          //   lbytes_eq mac2 sig_or_mac2
                          // )
                          // in

                        if (not (is_valid_sig_or_mac2)) then Fail IntegrityCheckFailed
                        else (
                          // Authenticate Initiator through cred_i and/or id_cred_i should be done here
                          // but this is ignored in this model!!!

                          // check if the Responder's credential is identical to the Initiator's credential.
                          // this check prevents Reflection Attack.
                          if (unequal_lbytes_eq cred_r cred_i)
                          then Fail InvalidCredential
                          else (
                            // And check if the received credential in the local list of Initiator
                            if (not (unequal_lbytes_eq #_ #(length is.remote_id_cred) cred_r is.remote_id_cred))
                            then Fail UnknownCredentialID
                            else
                              Res (ptx2, {hs with th2 = Some th2; g_xy = Some g_xy;
                                          prk3e2m = Some prk3e2m; g_y = Some g_y;
                                          prk2e = Some prk2e;
                                          })
                          )
                        )
                      )
        
      )
  

let initiator_send_msg3 #cs entr is hs ptx2 
  = (*----------------------- Constructing Message 3*)
  let th2 = Some?.v hs.th2 in
  let g_xy = Some?.v hs.g_xy in
  let prk3e2m = Some?.v hs.prk3e2m in
  // In real-world, the application should get credential payload, which
  // is locally stored, indexed by the CRED_ID
  let cred_r = ptx2.id_cred_r in
  // let g_y = (Some?.v hs.msg2).g_y in
  let g_y = Some?.v hs.g_y in

  let auth_method = hs.method in
  let auth_material = get_auth_material Initiator auth_method in

  let id_cred_i:lbytes (length is.id_cred) = is.id_cred in
  let cred_i = id_cred_i in
  // Compute TH3
  let th3 = compute_th3 th2 ptx2 cred_r in
      // get ephemeral-static DH share for implicit authentication
      let i = is.static_dh.priv in
      // derive PRK4e3m
      let prk4e3m_res:eresult (hash_out cs)
        = derive_prk4e3m #cs auth_material prk3e2m th3 (Some i) (Some g_y) in

      match prk4e3m_res with
        | Fail e -> Fail e
        | Res prk4e3m -> (
          // This model does not support EAD
          let ead3_op = None in
          // construct context3
          let ctx3 = construct_context3 id_cred_i th3 cred_i ead3_op in

          // compute MAC3
          let mac3 = expand_mac3 auth_material prk4e3m ctx3 in
          // compute Sig_or_MAC3
          let sk_i = is.signature_key.priv in
          let sig_or_mac3_op:option (sig_or_mac23_bytes cs auth_material)
            = derive_sig_or_mac3 #cs auth_material entr (Some sk_i) mac3 ctx3 in

          match sig_or_mac3_op with
            | None -> Fail SigningFailed
            | Some sig_or_mac3 -> (
              
              // construct plaintext3
              let ptx3 = construct_ptx3 id_cred_i sig_or_mac3 ead3_op in
              
              // encrypt plaintext3 get ciphertext3
              let ciphertext3 = encrypt_plaintext3 ptx3 th3 prk3e2m in
                  // compute TH4
                  let th4 = compute_th4 th3 ptx3 cred_i in
                      // derive PRK_out
                      let prk_out = expand_prk_out prk4e3m th4 in
                      // derive PRK_exporter
                      let prk_exporter = expand_prk_exporter prk_out in
                      // construct message3
                      let msg3:message3 = ciphertext3 in
                      

                      // return message3 as ciphertext3 and updated handshake state
                      let updated_hs = {hs with th3 = Some th3;
                                        th4 = Some th4;
                                        prk4e3m = Some prk4e3m;
                                        prk_out = Some prk_out;
                                        prk_exporter = Some prk_exporter;
                                      } in
                      (**) assert(msg3 == ciphertext3);
                      (**) assert(
                        let auth_material = get_auth_material Initiator auth_method in
                        let th3 = (Some?.v updated_hs.th3) in
                        let prk3e2m = (Some?.v updated_hs.prk3e2m) in
                        match (decrypt_ciphertext3 auth_material msg3 th3 prk3e2m) with
                          | Fail DecryptionFailed -> True
                          | Res decrypted_c3 -> (
                            if (not (is_valid_ptx3_size cs auth_material (length decrypted_c3)))
                            then False
                            else
                              (
                                let (id_cred_i, sig_or_mac3, ead3_op)
                                  = deserialize_ptx3_raw_bytes #cs #auth_material decrypted_c3 in
                                
                                let cred_i = id_cred_i in
                                let ptx3 = construct_ptx3 id_cred_i sig_or_mac3 ead3_op in
                                let th4 = compute_th4 th3 ptx3 cred_i in

                                Seq.equal (serialize_ptx3 ptx3) decrypted_c3
                                /\ lbytes_eq th4 (Some?.v updated_hs.th4)
                              )
                          )
                          | Fail _ -> False
                        );

                      Res (msg3, updated_hs)                  
                
            )
        )
    
(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)

/// Verify Sig_or_MAC3
let verify_sig_or_mac3 (#cs:supported_cipherSuite)
  (auth_material:authentication_material)
  (sig_or_mac3:lbytes (sig_or_mac23_size cs auth_material))
  (mac3:lbytes (mac23_size cs auth_material))
  (c3:context3 #cs)
  (pk_i_op:option (ec_signature_pub_key cs){
    auth_material == Signature ==> Some? pk_i_op
  })
  : bool
  = let ead3_op = c3.ead3 in
  let id_cred_i = c3.id_cred_i in
  let cred_i = c3.cred_i in
  let th3 = c3.th3 in
  
  match auth_material with
      | Signature -> (
        assert(length sig_or_mac3 = signature_size);
        let to_be_verified = match ead3_op with
            | None -> id_cred_i @< th3 @< cred_i @< mac3
            | Some ead3 -> (
              let ead3_lbytes:lbytes (length ead3) = ead3 in
              id_cred_i @< th3 @< cred_i @< ead3_lbytes @< mac3
            )
            in

        // let pk_i = rs.remote_signature_pub_key in
        let pk_i = Some?.v pk_i_op in
        ecdsa_verify to_be_verified pk_i sig_or_mac3
      )
      | MAC -> (
        assert(length sig_or_mac3 = mac23_size cs auth_material);
        lbytes_eq mac3 sig_or_mac3
      )

let responder_process_msg1 #cs rs msg1
  = 
  // Cipher Suite negotitiation.
  // At this moment, assume that Responder accepts
  // any proposed cipher suite from Initiator
  // assert (hs.method == msg1.method);
  // assert (hs.suite_i == msg1.suite_i);
  
  // Check if the Responder supports the cipher suite that
  // Initiator proposed. Basically, checking if the `suite_i`
  // in the list of supported cipher suites `rs.suites`
  let cs_label = (get_supportedCipherSuite_label cs) in
  // if (not (mem msg1.suite_i rs.suites) || cs_label <> msg1.suite_i) then Fail UnsupportedCipherSuite
  if (( msg1.suite_i <> rs.suites || cs_label <> msg1.suite_i))
  then Fail UnsupportedCipherSuite
  else (
    assert (msg1.suite_i = cs_label);
    let msg1_hash = do_hash cs (concat_msg1 msg1) in
    let hs:handshake_state #cs = init_handshake_state cs msg1.method msg1.g_x msg1_hash in
    // Res ({hs with msg1 = Some msg1})
    Res hs
  )

/// Intermediate-private function: derive Signature2
let derive_sig_or_mac2 (#cs:supported_cipherSuite)
  (auth_material:authentication_material)
  (entr: HACLRandom.entropy)
  (sk_r_op:option (ec_signature_priv_key cs){
    auth_material == Signature ==> Some? sk_r_op
  })
  (mac2:lbytes (mac23_size cs auth_material))
  (c2:context2 #cs)
  :option (sig_or_mac23_bytes cs auth_material)
  = let ead2_op = c2.ead2 in
  let id_cred_r = c2.id_cred_r in
  let cred_r = c2.cred_r in
  let th2 = c2.th2 in

  match auth_material with
    | MAC -> Some mac2
    | Signature -> (
      let to_be_signed = match ead2_op with
                | None -> id_cred_r @< th2 @< cred_r @< mac2
                | Some ead2 -> (
                  let ead2_lbytes:lbytes (length ead2) = ead2 in
                  id_cred_r @< th2 @< cred_r @< ead2_lbytes @< mac2
                )
                in
      let sk_r = Some?.v sk_r_op in
      let (entr3, nonce) = HACLRandom.crypto_random entr nonceP256_size in
      ecdsa_sign (Some nonce) to_be_signed sk_r
    )

 
// #push-options "--z3rlimit 10 --max_fuel 8 --max_ifuel 8"
let responder_send_msg2 #cs entr rs hs
  = let local_auth_material = get_auth_material Responder hs.method in
  // let msg1 = Some?.v hs.msg1 in
  let eph_ec_keypair = generate_ec_keypair cs entr in
  match eph_ec_keypair with
    | None -> Fail InvalidECPoint
    | Some (y_gy, entr1) -> (
      let y = y_gy.priv in
      let g_y = y_gy.pub in
      // let g_x = msg1.g_x in
      let g_x = hs.g_x in
      let (entr2, c_r) = HACLRandom.crypto_random entr1 c_id_size in
      match (dh y g_x) with
        | None -> Fail InvalidECPoint
        | Some g_xy -> (
          let id_cred_r:lbytes (length rs.id_cred) = rs.id_cred in
          let cred_r:lbytes (length rs.id_cred) = rs.id_cred in
          // construct EAD2: currently set it to None
          let ead2_op = None in
          // compute TH2
          // let th2 = compute_th2 msg1 g_y in
          let th2 = compute_th2_pre_hash #cs hs.msg1_hash g_y in
          // derive PRK2e
          let prk2e = extract_prk2e th2 g_xy in
          
          // derive PRK3e2m
          let prk3e2m_res:eresult (hash_out cs)
            = derive_prk3e2m #cs local_auth_material prk2e th2 (Some rs.static_dh.priv) (Some hs.g_x) in

          match prk3e2m_res with
            | Fail e -> Fail e
            | Res prk3e2m -> (
              // construct context2
              let ctx2 = construct_context2 c_r cred_r th2 cred_r ead2_op in
              // compute MAC2
              // let mac2_either = expand_mac2 auth_material prk3e2m ctx2 in
              let mac2 = expand_mac2 local_auth_material prk3e2m ctx2 in
              let sk_r = rs.signature_key.priv in
              let sig_or_mac2_op
                  = derive_sig_or_mac2 #cs local_auth_material entr2 (Some sk_r) mac2 ctx2 in
                // = match local_auth_material with
                //     | Signature -> (
                //       // use signature key for authentication from Responder side
                //       let sk_r = rs.signature_key.priv in
                //       derive_sig2 #cs entr2 sk_r mac2 ctx2                       
                //     )
                //     | MAC -> (
                //       // use static DH key for authentication from Responder side
                //       Some mac2
                //     )
                //   in

              match sig_or_mac2_op with
                | None -> Fail SigningFailed
                | Some sig_or_mac2 -> (
                  // construct plaintext2
                  let ptx2 = construct_ptx2 c_r id_cred_r sig_or_mac2 ead2_op in
                  
                  // (**) assert(concat_ptx2_get_length ptx2 = min_ptx2_size cs auth_material);
                  // encrypt plaintext2
                  let ciphertext2 = encrypt_plaintext2 ptx2 th2 prk2e in
                  // (**) assert(length ciphertext2 = min_ptx2_size cs auth_material);
                  // construct message2
                  let msg2 = construct_msg2 g_y ciphertext2 in
                  // update Handshake and Party state if applicable
                  let updated_hs = {hs with th2 = Some th2; g_y = Some g_y;
                                            g_xy = Some g_xy; prk3e2m = Some prk3e2m;
                                            prk2e = Some prk2e;
                                    }
                                    in
                  let updated_rs = {rs with eph_ec_keypair = Some y_gy;} in

                  Res (ptx2, msg2, updated_rs, updated_hs)
                  
                )
                    
              
            )
            
        )
    
    )
// #pop-options


let responder_process_msg3 #cs rs hs ptx2 msg3
  = let th2 = Some?.v hs.th2 in
  let prk3e2m = (Some?.v hs.prk3e2m) in
  let ciphertext3 = msg3 in
  // checking auth_material and auth_method consistence
  let auth_method = hs.method in
  let auth_material = get_auth_material Responder auth_method in
  let remote_auth_material = get_auth_material Initiator auth_method in

  let id_cred_r:lbytes (length rs.id_cred) = rs.id_cred in
  let cred_r = id_cred_r in

  // Compute TH3
  let th3 = compute_th3 th2 ptx2 cred_r in
      // At this point it is guaranteed that authentication method
      // and authentication material are matched
      let ptx3_serialized_bytes_res = decrypt_ciphertext3 remote_auth_material ciphertext3 th3 prk3e2m in
      match ptx3_serialized_bytes_res with
        | Fail e -> Fail SerializationDeserializationFailed
        | Res ptx3_serialized_bytes -> (
          if (not (is_valid_ptx3_size cs remote_auth_material (length ptx3_serialized_bytes)))
          then Fail SerializationDeserializationFailed
          else
          let (id_cred_i_bytes, sig_or_mac3_raw, ead3_op) = deserialize_ptx3_raw_bytes #cs #remote_auth_material ptx3_serialized_bytes in

              let id_cred_i:lbytes (length id_cred_i_bytes) = id_cred_i_bytes in
              let cred_i = id_cred_i in

              // convert sig_or_mac3 raw bytes to type sig_or_mac23_bytes
              // let sig_or_mac3_op = bytes_to_sig_or_mac23_bytes cs remote_auth_material sig_or_mac3_raw in
              let sig_or_mac3 = sig_or_mac3_raw in
                  // construct plaintext3 from component bytes
                  let ptx3 = construct_ptx3 id_cred_i sig_or_mac3 ead3_op in
                  // construct context3
                  let ctx3 = construct_context3 id_cred_i th3 cred_i ead3_op in

                  // derive PRK4e3m
                  let y = (Some?.v rs.eph_ec_keypair).priv in
                  let g_i = rs.remote_static_pub_key in
                  let prk4e3m_res:eresult (hash_out cs)
                    = derive_prk4e3m #cs remote_auth_material prk3e2m th3 (Some y) (Some g_i) in
                    // = match remote_auth_material with
                    //   | Signature -> Res prk3e2m
                    //   | MAC -> (
                    //     // get ephemeral-static DH share for implicit authentication
                    //     let y = (Some?.v rs.eph_ec_keypair).priv in
                    //     let g_i = rs.remote_static_pub_key in
                    //     let ephe_stat_shared = dh y g_i in
                    //     match ephe_stat_shared with
                    //       | None -> Fail InvalidECPoint
                    //       | Some g_iy -> (
                    //         // derive SALT4e3m
                    //         let salt4e3m = expand_salt4e3m prk3e2m th3 in
                    //         Res (extract_prk4e3m salt4e3m g_iy)
                    //       )
                    //   )
                    //   in

                  match prk4e3m_res with
                    | Fail e -> Fail e
                    | Res prk4e3m -> (
                      // compute mac3
                      let mac3 = expand_mac3 remote_auth_material prk4e3m ctx3 in
                      // verify sig_or_mac3
                      // let is_valid_sig_or_mac3 = match sig_or_mac3 with
                      //   | Inl signature -> (
                      //     let to_be_verified = match ead3_op with
                      //                           | None -> id_cred_i @< th3 @< cred_i @< mac3
                      //                           | Some ead3 -> id_cred_i @< th3 @< cred_i @< ead3 @< mac3
                      //                           in
                      //     let pk_i = rs.remote_signature_pub_key in
                      //     ecdsa_verify to_be_verified pk_i signature
                      //   )
                      //   | Inr rev_mac3 -> (
                      //     lbytes_eq mac3 rev_mac3
                      //   )
                      //   in

                      let pk_i = rs.remote_signature_pub_key in
                      let is_valid_sig_or_mac3
                        = verify_sig_or_mac3 #cs remote_auth_material sig_or_mac3 mac3 ctx3 (Some pk_i) in
                        // = match remote_auth_material with
                        // | Signature -> (
                        //   assert(length sig_or_mac3 = signature_size);
                        //   let to_be_verified = match ead3_op with
                        //       | None -> id_cred_i @< th3 @< cred_i @< mac3
                        //       | Some ead3 -> (
                        //         let ead3_lbytes:lbytes (length ead3) = ead3 in
                        //         id_cred_i @< th3 @< cred_i @< ead3_lbytes @< mac3
                        //       )
                        //       in
                        //   let pk_i = rs.remote_signature_pub_key in
                        //   ecdsa_verify to_be_verified pk_i sig_or_mac3
                        // )
                        // | MAC -> (
                        //   assert(length sig_or_mac3 = mac23_size cs remote_auth_material);
                        //   lbytes_eq mac3 sig_or_mac3
                        // )
                        // in
                      
                      if (not (is_valid_sig_or_mac3)) then Fail IntegrityCheckFailed
                      else (
                        // Authenticate Initator through cred_i and/or id_cred_i should be done here
                        // but this is ignored in this model!!!

                        // check if the Responder's credential is identical to the Initiator's credential.
                        // this check prevents Reflection Attack.
                        if (unequal_lbytes_eq cred_r cred_i) then Fail InvalidCredential
                        else (
                          // And check if the received credential in the local list of Responder
                          if (not (unequal_lbytes_eq #_ #(length rs.remote_id_cred) cred_i rs.remote_id_cred))
                          then Fail UnknownCredentialID
                          else
                            // compute TH4
                            let th4 = compute_th4 th3 ptx3 cred_i in
                      
                            // derive PRK_out
                            let prk_out = expand_prk_out prk4e3m th4 in
                            // derive prk_exporter
                            let prk_exporter = expand_prk_exporter prk_out in
                            
                            Res ({hs with th3 = Some th3; th4 = Some th4;
                                          prk4e3m = Some prk4e3m;
                                          prk_out = Some prk_out;
                                          prk_exporter = Some prk_exporter;})
                            
                        )
                        
                      )
                    )

        )
