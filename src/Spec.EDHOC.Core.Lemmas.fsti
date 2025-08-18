module Spec.EDHOC.Core.Lemmas

open Spec.EDHOC.Core
open Spec.EDHOC.CryptoPrimitives
open Spec.EDHOC.Base.Definitions
open Spec.EDHOC.Parser
open Spec.EDHOC.CommonPred
open Spec.EDHOC.Ciphertext
open Spec.EDHOC.TranscriptHash
open Spec.EDHOC.KeySchedule

(*HACL libs*)
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

module HACLRandom = Lib.RandomSequence
module Seq = Lib.Sequence

/// --------------------------
/// Initiator send Msg1 lemmas
/// --------------------------

val lemma_initiator_send_msg1_responds:
  cs:supported_cipherSuite
  -> method:method_enum
  -> entr: HACLRandom.entropy
  -> is:party_state #cs
  -> Lemma (ensures (
    let res_gen_key = generate_ec_keypair cs entr in
    match (initiator_send_msg1 cs method entr is) with
      | Res (msg1_ab, is_shared_est, hs_i_after_msg1_ab) -> (
        let eph_kp = Some?.v is_shared_est.eph_ec_keypair in

        let x_gx_res = generate_ec_keypair cs entr in

        match x_gx_res with
          | None -> False
          | Some (x_gx, entr1) -> (
            Some? res_gen_key /\ ~(Some? msg1_ab.ead1)
            /\ Seq.equal msg1_ab.g_x hs_i_after_msg1_ab.g_x
            /\ Seq.equal hs_i_after_msg1_ab.g_x eph_kp.pub
            /\ Seq.equal eph_kp.priv x_gx.priv
            /\ Seq.equal eph_kp.pub x_gx.pub
          )
      )

      | Fail InvalidECPoint -> ~(Some? res_gen_key)
      | Fail _ -> False
  ))
  [SMTPat (initiator_send_msg1 cs method entr is)]

val lemma_initiator_send_msg1_consistence:
  cs:supported_cipherSuite
  -> method:method_enum
  -> entr: HACLRandom.entropy
  -> is:party_state #cs
  -> Lemma (ensures (
    lemma_initiator_send_msg1_responds cs method entr is;
    match (initiator_send_msg1 cs method entr is) with
      | Fail InvalidECPoint -> true
      | Res (msg1, is', hs_i) -> (
        let x = (Some?.v is'.eph_ec_keypair).priv in
        let g_x = (Some?.v is'.eph_ec_keypair).pub in
        let msg1_hash = do_hash cs (concat_msg1 msg1) in
        
        msg1.method = method /\ hs_i.method = method
        /\ unequal_lbytes_eq msg1.g_x g_x
        /\ lbytes_eq hs_i.g_x g_x
        // /\ normalize_term msg1 == normalize_term (Some?.v hs_i.msg1)
        /\ lbytes_eq msg1_hash hs_i.msg1_hash
        /\ post_ps_unchanged_fixed_vals is is'
      )
  ))
  [SMTPat (initiator_send_msg1 cs method entr is)]


/// --------------------------
/// Responder process Msg1 lemmas
/// --------------------------

val lemma_responder_process_msg1_agreement:
  #cs:supported_cipherSuite
  -> rs:party_state #cs
  -> msg1:message1 #cs
  -> Lemma (ensures (
    match (responder_process_msg1 rs msg1) with
      | Fail UnsupportedCipherSuite -> True
      | Res (hs) -> (
        msg1.method = hs.method
        /\ (msg1.suite_i = rs.suites)
        /\ msg1.suite_i = hs.suite_i
        // /\ normalize_term msg1 == normalize_term (Some?.v hs.msg1)
        /\ equal msg1.g_x hs.g_x
        /\ equal (do_hash cs (concat_msg1 msg1)) hs.msg1_hash
      )
      | Fail _ -> False
  ))
  [SMTPat (responder_process_msg1 rs msg1)]

/// --------------------------
/// Responder send Msg2 lemmas
/// --------------------------

val lemma_responder_send_msg2_respond:
  #cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> rs:party_state #cs
  -> hs:handshake_state_after_msg1 #cs
  -> Lemma (ensures (
    match (responder_send_msg2 #cs entr rs hs) with
      | Fail InvalidECPoint
      | Fail SerializationDeserializationFailed
      | Fail SigningFailed -> true
      | Res (ptx2, msg2, rs', hs_r'') -> (
        valid_hs_msg1_to_msg2 hs hs_r''
        /\ post_ps_unchanged_fixed_vals rs rs'
        /\ (
          match (get_auth_material Responder hs.method) with
          | Signature -> true
          | MAC ->
              Option.isSome (dh rs.static_dh.priv hs.g_x) 
        )
        
      )
      | Fail _ -> false
  ))
  [SMTPat (responder_send_msg2 #cs entr rs hs)]

val lemma_responder_send_msg2_consistence:
  #cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> rs:party_state #cs
  -> hs:handshake_state_after_msg1 #cs
  -> Lemma (ensures (
    match (responder_send_msg2 #cs entr rs hs) with
      | Fail InvalidECPoint
      | Fail SerializationDeserializationFailed
      | Fail SigningFailed -> true
      | Res (ptx2, msg2, rs', hs'') -> (
        // let th2 = Some?.v hs''.th2 in
        // let th2 = compute_th2 (Some?.v hs.msg1) msg2.g_y in
        let th2 = compute_th2_pre_hash #cs hs.msg1_hash msg2.g_y in
        let g_xy = Some?.v hs''.g_xy in
        let prk2e = extract_prk2e th2 g_xy in
        let prk3e2m = match (get_auth_material Responder hs.method) with
                        | Signature -> prk2e
                        | MAC -> (
                          let r = rs.static_dh.priv in
                          // let g_x = (Some?.v hs.msg1).g_x in
                          let g_x = hs.g_x in
                          let g_rx = Some?.v (dh r g_x) in
                          let salt3e2m = expand_salt3e2m prk2e th2 in
                          extract_prk3e2m salt3e2m g_rx
                        ) in

        lbytes_eq msg2.g_y (Some?.v rs'.eph_ec_keypair).pub
        /\ unequal_lbytes_eq #(length ptx2.id_cred_r) #(length rs.id_cred) ptx2.id_cred_r rs.id_cred
        /\ unequal_lbytes_eq (Some?.v hs''.prk2e) prk2e
        /\ unequal_lbytes_eq (Some?.v hs''.prk3e2m) prk3e2m
        /\ valid_hs_msg1_to_msg2 hs hs''
        // /\ normalize_term (Some?.v hs.msg1) == normalize_term (Some?.v hs''.msg1)
        /\ unequal_lbytes_eq (Some?.v hs''.th2) th2
        // /\ normalize_term (Some?.v hs''.msg2) == normalize_term msg2
      )
  ))
  [SMTPat (responder_send_msg2 #cs entr rs hs)]

/// --------------------------
/// Initiator process Msg2 lemmas
/// --------------------------

val lemma_initiator_process_msg2_respond:
  #cs:supported_cipherSuite
  -> is:party_state_shared_est #cs
  -> hs:handshake_state_after_msg1 #cs
  -> msg2:message2 #cs
  -> Lemma (ensures (
    match (initiator_process_msg2 #cs is hs msg2) with
      | Fail InvalidECPoint
      | Fail SerializationDeserializationFailed
      | Fail IntegrityCheckFailed
      | Fail UnknownCredentialID
      | Fail InvalidCredential -> true
      | Res (ptx2, hs_i'') -> (
        valid_hs_msg1_to_msg2 hs hs_i''
        /\ (
          match (get_auth_material Responder hs.method) with
          | Signature -> true
          | MAC -> Option.isSome (dh (Some?.v is.eph_ec_keypair).priv is.remote_static_pub_key)
        )
        
      )
      | Fail _ -> false
  ))
  [SMTPat (initiator_process_msg2 #cs is hs msg2)]

val lemma_initiator_process_msg2_consistence:
  #cs:supported_cipherSuite
  -> is:party_state_shared_est #cs
  -> hs:handshake_state_after_msg1 #cs
  -> msg2:message2 #cs
  -> Lemma (ensures (
    match (initiator_process_msg2 #cs is hs msg2) with
      | Fail InvalidECPoint
      | Fail SerializationDeserializationFailed
      | Fail IntegrityCheckFailed
      | Fail UnknownCredentialID
      | Fail InvalidCredential -> true
      | Res (ptx2, hs'') -> (
        // let th2 = Some?.v hs''.th2 in
        // let th2 = compute_th2 (Some?.v hs''.msg1) msg2.g_y in
        let th2 = compute_th2_pre_hash #cs (hs.msg1_hash) msg2.g_y in
        let x = (Some?.v is.eph_ec_keypair).priv in

        match (dh x msg2.g_y) with
          | None -> False
          | Some g_xy -> (
            let prk2e = (extract_prk2e th2 g_xy) in
            let prk3e2m = match (get_auth_material Responder hs.method) with
                            | Signature -> prk2e
                            | MAC -> (
                              let g_r = is.remote_static_pub_key in
                              let x = (Some?.v is.eph_ec_keypair).priv in
                              let g_rx = Some?.v (dh x g_r) in
                              let salt3e2m = expand_salt3e2m prk2e th2 in
                              extract_prk3e2m salt3e2m g_rx
                            ) in
            
            unequal_lbytes_eq (Some?.v hs''.th2) th2
            /\ unequal_lbytes_eq (Some?.v hs''.prk2e) prk2e
            /\ unequal_lbytes_eq (Some?.v hs''.g_xy) g_xy
            /\ unequal_lbytes_eq (Some?.v hs''.prk3e2m) prk3e2m
            /\ valid_hs_msg1_to_msg2 hs hs''
            // /\ normalize_term (Some?.v hs.msg1) == normalize_term (Some?.v hs''.msg1)
            // /\ normalize_term (Some?.v hs''.msg2) == normalize_term msg2
          )
      )
  ))
  [SMTPat (initiator_process_msg2 #cs is hs msg2)]

/// --------------------------
/// Integration Msg1 and Msg2 lemmas
/// --------------------------

/// Requires two parties have valid credentials of the other one
/// and authentication keys (static DH/signature key).
let precondition_integration_party_states
  (#cs:supported_cipherSuite) (is:party_state #cs) (rs:party_state #cs) (method:method_enum)
  = let cs_label = get_supportedCipherSuite_label cs in
  let r = rs.static_dh.priv in
  let i = is.static_dh.priv in

  let g_r_op = secret_to_public r in
  let g_i_op = secret_to_public i in

  (Option.isSome g_r_op) /\ (Option.isSome g_i_op)
  /\ (
    let g_r = Some?.v g_r_op in
    let g_i = Some?.v g_i_op in

    // set up g_r
    (unequal_lbytes_eq is.remote_static_pub_key rs.static_dh.pub)
    /\ (unequal_lbytes_eq is.remote_static_pub_key g_r)
    /\ (unequal_lbytes_eq is.remote_signature_pub_key rs.signature_key.pub)
    
    // set up g_i
    /\ (unequal_lbytes_eq rs.remote_static_pub_key is.static_dh.pub)
    /\ (unequal_lbytes_eq rs.remote_static_pub_key g_i)
    /\ (unequal_lbytes_eq rs.remote_signature_pub_key is.signature_key.pub)
  )

val lemma_integration_msg1_msg2_eph_stat_share:
  #cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> is:party_state #cs
  -> rs:party_state #cs
  -> method:method_enum
  -> Lemma (requires (
    precondition_integration_party_states is rs method
))
    (ensures (
      match (initiator_send_msg1 cs method entr is) with
        | Fail _ -> true
        | Res (msg1, is', hs_i') -> (
          match (responder_process_msg1 #cs rs msg1) with
            | Fail _ -> true
            | Res (hs_r') -> (
              
              match (responder_send_msg2 #cs entr rs hs_r') with
                | Fail _ -> true
                | Res (ptx2_r, msg2, rs', hs_r'') -> (
                  match (initiator_process_msg2 #cs is' hs_i' msg2) with
                    | Fail _ -> true
                    | Res (ptx2_i, hs_i'') -> (

                        (
                            match (get_auth_material Responder method) with
                              | Signature -> true
                              | MAC -> (
                                let r = rs'.static_dh.priv in
                                let x = (Some?.v is'.eph_ec_keypair).priv in

                                // let g_x = (Some?.v hs_r''.msg1).g_x in
                                let g_x = hs_r''.g_x in
                                let g_r = is'.remote_static_pub_key in

                                let g_xr = Some?.v (dh r g_x) in
                                let g_rx = Some?.v (dh x g_r) in

                                lbytes_eq g_xr g_rx

                                
        ))))))
    ))


val lemma_integration_msg1_msg2_consistence:
  #cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> is:party_state #cs
  -> rs:party_state #cs
  -> method:method_enum
  -> Lemma (requires (
      precondition_integration_party_states is rs method
  ))
    (ensures (

      match (initiator_send_msg1 cs method entr is) with
        | Fail _ -> true
        | Res (msg1, is', hs_i') -> (
          match (responder_process_msg1 #cs rs msg1) with
            | Fail _ -> true
            | Res (hs_r') -> (
              lemma_responder_process_msg1_agreement #cs rs msg1;
              let msg1_agreement = (
                post_hs_after_msg1 #cs hs_i' hs_r'
                /\ hs_r'.method = method
                /\ lbytes_eq msg1.g_x (Some?.v is'.eph_ec_keypair).pub
              ) in
              
              
              match (responder_send_msg2 #cs entr rs hs_r') with
                | Fail _ -> true
                | Res (ptx2_r, msg2, rs', hs_r'') -> (

                  match (initiator_process_msg2 #cs is' hs_i' msg2) with
                    | Fail _ -> true
                    | Res (ptx2_i, hs_i'') -> (

                      let msg2_agreement = (               
                        post_hs_after_msg2 #cs hs_i'' hs_r''
                        /\ hs_r''.method = method
                        /\ normalize_term ptx2_i == normalize_term ptx2_r
                        /\ unequal_lbytes_eq (concat_ptx2 ptx2_i) (concat_ptx2 ptx2_r)
                      ) in

                      msg1_agreement /\ msg2_agreement
                      /\ valid_hs_msg1_to_msg2 hs_i' hs_i''
                      /\ valid_hs_msg1_to_msg2 hs_r' hs_r''

                    )
                )
            )
        )
    ))

val bundle_msg1_msg2:
  #cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> is:party_state #cs
  -> rs:party_state #cs
  -> method:method_enum
  -> (eresult (plaintext2 #cs #(get_auth_material Responder method)
              & plaintext2 #cs #(get_auth_material Responder method)
              & message2 #cs #(get_auth_material Responder method)
              & party_state_shared_est #cs & party_state_shared_est #cs
              & handshake_state_after_msg2 #cs
              & handshake_state_after_msg2 #cs))

val lemma_bundle_msg1_msg2:
  #cs:supported_cipherSuite
  -> entr:HACLRandom.entropy
  -> is:party_state #cs
  -> rs:party_state #cs
  -> method:method_enum
  -> Lemma (requires precondition_integration_party_states is rs method)
  (ensures (
    match (bundle_msg1_msg2 #cs entr is rs method) with
      | Fail _ -> True
      | Res (ptx2_i, ptx2_r, msg2, is', rs', hs_i'', hs_r'') ->
        post_hs_after_msg2 #cs hs_i'' hs_r''
        /\ hs_r''.method = method
        /\ hs_i''.method = method
        /\ normalize_term ptx2_i == normalize_term ptx2_r
        /\ unequal_lbytes_eq (concat_ptx2 ptx2_i) (concat_ptx2 ptx2_r)
        /\ post_ps_unchanged_fixed_vals is is'
        /\ post_ps_unchanged_fixed_vals rs rs'
  ))
  [SMTPat (bundle_msg1_msg2 #cs entr is rs method)]

/// --------------------------
/// Initiator send Msg3 lemmas
/// --------------------------
val lemma_initiator_send_msg3_respond:
  #cs:supported_cipherSuite
  -> entr:HACLRandom.entropy
  -> is:party_state_shared_est #cs
  -> hs:handshake_state_after_msg2 #cs
  -> ptx2:plaintext2 #cs #(get_auth_material Responder hs.method)
  -> Lemma (ensures (
    match (initiator_send_msg3 entr is hs ptx2) with
      | Fail SerializationDeserializationFailed
      | Fail SigningFailed
      | Fail InvalidECPoint -> true
      | Fail _ -> false
      | Res (msg3, hs_i''') -> (
        valid_hs_msg2_to_msg3 hs hs_i'''
        /\ (
          match (get_auth_material Initiator hs.method) with
          | Signature -> true
          | MAC -> (
            // Option.isSome (dh is.static_dh.priv (Some?.v hs.msg2).g_y)
            Option.isSome (dh is.static_dh.priv (Some?.v hs.g_y))
          )
        )
      )
  ))
  [SMTPat (initiator_send_msg3 #cs entr is hs ptx2)]

val lemma_initiator_send_msg3_respond_component_equiv:
  #cs:supported_cipherSuite
  -> entr:HACLRandom.entropy
  -> is:party_state_shared_est #cs
  -> hs:handshake_state_after_msg2 #cs
  -> ptx2:plaintext2 #cs #(get_auth_material Responder hs.method)
  -> Lemma (ensures (
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
    let i = is.static_dh.priv in

    let res_prk4e3m = derive_prk4e3m #cs auth_material prk3e2m th3 (Some i) (Some g_y) in
    let res_tot = initiator_send_msg3 #cs entr is hs ptx2 in

    (Fail? res_prk4e3m ==> Fail? res_tot)
    /\ (Res? res_prk4e3m ==> (
      match res_prk4e3m with Res prk4e3m ->
        // This model does not support EAD
        let ead3_op = None in
        // construct context3
        let ctx3 = construct_context3 id_cred_i th3 cred_i ead3_op in

        // compute MAC3
        let mac3 = expand_mac3 auth_material prk4e3m ctx3 in
        // compute Sig_or_MAC3
        let sk_i = is.signature_key.priv in

        let sig_or_mac3_op
          = derive_sig_or_mac3 #cs auth_material entr (Some sk_i) mac3 ctx3 in

        Some? sig_or_mac3_op <==> Res? res_tot
        /\ (Res? res_tot <==> (Res? res_prk4e3m /\ Some? sig_or_mac3_op))
    ))
  ))
  [SMTPat (initiator_send_msg3 #cs entr is hs ptx2)]

val lemma_initiator_send_msg3_functional_correctness:
  #cs:supported_cipherSuite
  -> entr:HACLRandom.entropy
  -> is:party_state_shared_est #cs
  -> hs:handshake_state_after_msg2 #cs
  -> ptx2:plaintext2 #cs #(get_auth_material Responder hs.method)
  -> Lemma (ensures (
    let res_tot = initiator_send_msg3 #cs entr is hs ptx2 in

    Res? res_tot ==> (
      match res_tot with Res (msg3, hs''') -> (
        let auth_material = get_auth_material Initiator hs.method in
        let th3 = (Some?.v hs'''.th3) in
        let prk3e2m = (Some?.v hs'''.prk3e2m) in
        match (decrypt_ciphertext3 auth_material msg3 th3 prk3e2m) with
          | Fail DecryptionFailed -> True
          | Res decrypted_c3 -> (
            if (not (is_valid_ptx3_size cs auth_material (length decrypted_c3)))
            then False
            else (
              let (id_cred_i, sig_or_mac3, ead3_op)
                = deserialize_ptx3_raw_bytes #cs #auth_material decrypted_c3 in
              
              let cred_i = id_cred_i in
              let ptx3 = construct_ptx3 id_cred_i sig_or_mac3 ead3_op in
              let th4 = compute_th4 th3 ptx3 cred_i in

              // derive prk4e3m
              let g_y = Some?.v hs.g_y in
              let i = is.static_dh.priv in

              let res_prk4e3m
                = derive_prk4e3m #cs auth_material prk3e2m th3 (Some i) (Some g_y) in
              match res_prk4e3m with
                | Fail _ -> False
                | Res prk4e3m -> (
                  // derive sig_or_mac3
                  let ctx3 = construct_context3 id_cred_i th3 cred_i ead3_op in
                  let mac3 = expand_mac3 auth_material prk4e3m ctx3 in
                  let sk_i = is.signature_key.priv in

                  let res_sig_or_mac3
                    = derive_sig_or_mac3 #cs auth_material entr (Some sk_i) mac3 ctx3 in
                  match res_sig_or_mac3 with
                    | None -> False
                    | Some computed_sig_or_mac3 -> (
                      let prk_out = expand_prk_out prk4e3m th4 in
                      let prk_exporter = expand_prk_exporter prk_out in

                      length (serialize_ptx3 ptx3) == length decrypted_c3
                      /\ Seq.equal (serialize_ptx3 ptx3) decrypted_c3
                      /\ None? ead3_op
                      /\ lbytes_eq th4 (Some?.v hs'''.th4)
                      /\ lbytes_eq prk4e3m (Some?.v hs'''.prk4e3m)
                      /\ lbytes_eq sig_or_mac3 computed_sig_or_mac3
                      /\ lbytes_eq prk_out (Some?.v hs'''.prk_out)
                      /\ lbytes_eq prk_exporter (Some?.v hs'''.prk_exporter)
                    )

                )
            )
          )
          | Fail _ -> False
      )
    )
  ))
  [SMTPat (initiator_send_msg3 #cs entr is hs ptx2)]

val lemma_initiator_send_msg3_consistence:
  #cs:supported_cipherSuite
  -> entr:HACLRandom.entropy
  -> is:party_state_shared_est #cs
  -> hs:handshake_state_after_msg2 #cs
  -> ptx2:plaintext2 #cs #(get_auth_material Responder hs.method)
  -> Lemma (ensures (
    match (initiator_send_msg3 entr is hs ptx2) with
      | Fail SerializationDeserializationFailed
      | Fail SigningFailed
      | Fail InvalidECPoint -> true
      | Fail _ -> false
      | Res (msg3, hs''') -> (
        let th2 = Some?.v hs.th2 in
        let cred_r = ptx2.id_cred_r in
        let th3 = compute_th3 th2 ptx2 cred_r in
        // let th3 = Some?.v hs'''.th3 in
        let prk3e2m = Some?.v hs'''.prk3e2m in
        // let th3 = Some?.v hs'''.th3 in
        let prk4e3m = match (get_auth_material Initiator hs.method) with
                      | Signature -> prk3e2m
                      | MAC -> (
                        let i = is.static_dh.priv in
                        // let g_y = (Some?.v hs.msg2).g_y in
                        let g_y = Some?.v hs.g_y in
                        let g_iy = Some?.v (dh i g_y) in
                        let salt4e3m = expand_salt4e3m prk3e2m th3 in
                        extract_prk4e3m salt4e3m g_iy
                      ) in
        let th4 = Some?.v hs'''.th4 in
        let prk_out = expand_prk_out prk4e3m th4 in
        let prk_exporter = expand_prk_exporter prk_out in

        lbytes_eq (Some?.v hs'''.th3) th3
        /\ valid_hs_msg2_to_msg3 hs hs'''
        /\ lbytes_eq (Some?.v hs'''.prk4e3m) prk4e3m
        /\ lbytes_eq (Some?.v hs'''.prk_out) prk_out
        /\ lbytes_eq (Some?.v hs'''.prk_exporter) prk_exporter
      
      )
  ))
  [SMTPat (initiator_send_msg3 #cs entr is hs ptx2)]


/// -----------------------------
/// Responder process Msg3 lemmas
/// -----------------------------
val lemma_responder_process_msg3_respond:
  #cs:supported_cipherSuite
  -> rs:party_state_shared_est #cs
  -> hs:handshake_state_after_msg2 #cs
  -> ptx2:plaintext2 #cs #(get_auth_material Responder hs.method)
  -> msg3:message3 #cs
  -> Lemma (ensures (
    match (responder_process_msg3 rs hs ptx2 msg3) with
      | Fail SerializationDeserializationFailed
      | Fail InvalidCredential
      | Fail IntegrityCheckFailed
      | Fail UnknownCredentialID
      | Fail InvalidECPoint -> true
      | Fail _ -> false
      | Res (hs_r''') -> (
        valid_hs_msg2_to_msg3 hs hs_r'''
        /\ (
          match (get_auth_material Initiator hs.method) with
          | Signature -> true
          | MAC -> (
            Option.isSome (dh (Some?.v rs.eph_ec_keypair).priv rs.remote_static_pub_key)
          )
        )
        
      )
  ))
  [SMTPat (responder_process_msg3 #cs rs hs ptx2 msg3)]

val lemma_responder_process_msg3_consistence:
  #cs:supported_cipherSuite
  -> rs:party_state_shared_est #cs
  -> hs:handshake_state_after_msg2 #cs
  -> ptx2:plaintext2 #cs #(get_auth_material Responder hs.method)
  -> msg3:message3 #cs
  -> Lemma (ensures (
    match (responder_process_msg3 rs hs ptx2 msg3) with
      | Fail SerializationDeserializationFailed
      | Fail InvalidCredential
      | Fail IntegrityCheckFailed
      | Fail UnknownCredentialID
      | Fail InvalidECPoint -> true
      | Fail _ -> false
      | Res (hs''') -> (
        let th2 = Some?.v hs.th2 in
        let cred_r = rs.id_cred in
        let th3 = compute_th3 th2 ptx2 cred_r in
            // let th3 = Some?.v hs'''.th3 in
            let prk3e2m = Some?.v hs'''.prk3e2m in
            // let th3 = Some?.v hs'''.th3 in
            let prk4e3m = match (get_auth_material Initiator hs.method) with
                          | Signature -> prk3e2m
                          | MAC -> (
                            let y = (Some?.v rs.eph_ec_keypair).priv in
                            let g_i = rs.remote_static_pub_key in
                            let g_iy = Some?.v (dh y g_i) in 
                            let salt4e3m = expand_salt4e3m prk3e2m th3 in
                            extract_prk4e3m salt4e3m g_iy
                          ) in
            let th4 = Some?.v hs'''.th4 in
            let prk_out = expand_prk_out prk4e3m th4 in
            let prk_exporter = expand_prk_exporter prk_out in

            lbytes_eq (Some?.v hs'''.th3) th3
            /\ lbytes_eq (Some?.v hs'''.prk4e3m) prk4e3m
            /\ lbytes_eq (Some?.v hs'''.prk_out) prk_out
            /\ lbytes_eq (Some?.v hs'''.prk_exporter) prk_exporter
            /\ valid_hs_msg2_to_msg3 hs hs'''
      )
  ))
  [SMTPat (responder_process_msg3 #cs rs hs ptx2 msg3)]

/// ---------------------------------------
/// Integration Msg1, Msg2, and Msg3 lemmas
/// ---------------------------------------
val bundle_msg1_msg3:
  #cs:supported_cipherSuite
  -> entr:HACLRandom.entropy
  -> is:party_state #cs
  -> rs:party_state #cs
  -> method:method_enum
  -> eresult (party_state_shared_est #cs
            & party_state_shared_est #cs
            & handshake_state_after_msg3 #cs
            & handshake_state_after_msg3 #cs)

val lemma_integration_msg1_msg3_eph_stat_share:
  #cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> is:party_state #cs
  -> rs:party_state #cs
  -> method:method_enum
  -> Lemma (requires (
    precondition_integration_party_states is rs method
  ))
  (ensures (
    match (bundle_msg1_msg2 #cs entr is rs method) with
      | Fail _ -> True
      | Res (ptx2_i, ptx2_r, msg2, is', rs', hs_i'', hs_r'') -> (
        
        match (initiator_send_msg3 #cs entr is' hs_i'' ptx2_i) with
          | Fail _ -> true
          | Res (msg3, hs_i''') -> (

            match (responder_process_msg3 #cs rs' hs_r'' ptx2_r msg3) with
              | Fail _ -> true
              | Res (hs_r''') -> (
                // assert(hs_r'''.method = hs_i'''.method);
                // assert(hs_r'''.method = method);
                match (get_auth_material Initiator method) with
                  | Signature -> true
                  | MAC -> (
                    let i = is'.static_dh.priv in
                    // let g_y = (Some?.v hs_i''.msg2).g_y in
                    let g_y = Some?.v hs_i''.g_y in

                    let y = (Some?.v rs'.eph_ec_keypair).priv in
                    let g_i = rs'.remote_static_pub_key in

                    let g_yi_res = dh i g_y in
                    let g_iy_res = dh y g_i in

                    match (g_yi_res, g_iy_res) with
                      | (None, _) | (_, None) -> False
                      | (Some g_yi, Some g_iy) -> (
                        lbytes_eq g_yi g_iy

                      )
                    // let g_iy = Some?.v (dh y g_i) in


                  )
              )
          )
      )
  ))

// #push-options"--max_fuel 8"
val lemma_bundle_msg1_msg3:
  #cs:supported_cipherSuite
  -> entr:HACLRandom.entropy
  -> is:party_state #cs
  -> rs:party_state #cs
  -> method:method_enum
  -> Lemma (requires precondition_integration_party_states is rs method)
  (ensures (
    match (bundle_msg1_msg3 #cs entr is rs method) with
      | Fail _ -> True
      | Res (is', rs', hs_i''', hs_r''') -> (
        post_hs_after_msg3 #cs hs_i''' hs_r'''
      )
  ))
  [SMTPat (bundle_msg1_msg3 #cs entr is rs method)]
// #pop-options

