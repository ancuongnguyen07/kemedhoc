module Spec.EDHOC.Core.Lemmas

friend Spec.EDHOC.Core
friend Spec.EDHOC.Ciphertext
friend Spec.EDHOC.Parser


(*------------------------------------*)
(*----------------------------- LEMMAS*)
(*------------------------------------*)

/// --------------------------
/// Initiator send Msg1 lemmas
/// --------------------------
let lemma_initiator_send_msg1_responds cs method entr is
  = ()

let lemma_initiator_send_msg1_consistence cs method entr is
  = lemma_initiator_send_msg1_responds cs method entr is;
  ()

/// --------------------------
/// Responder process Msg1 lemmas
/// --------------------------

let lemma_responder_process_msg1_agreement #cs rs msg1
  = ()

/// --------------------------
/// Responder send Msg2 lemmas
/// --------------------------

let lemma_responder_send_msg2_respond #cs entr rs hs
  = ()

// #push-options "--z3rlimit 25 --max_fuel 32 --max_ifuel 16"
let lemma_responder_send_msg2_consistence #cs entr rs hs
  = lemma_responder_send_msg2_respond #cs entr rs hs;
  ()

/// --------------------------
/// Initiator process Msg2 lemmas
/// --------------------------

let lemma_initiator_process_msg2_respond #cs is hs msg2
  = ()

let lemma_initiator_process_msg2_consistence #cs is hs msg2
  = lemma_initiator_process_msg2_respond #cs is hs msg2;
  ()


/// --------------------------------
/// Integration Msg1 and Msg2 lemmas
/// --------------------------------
let lemma_integration_msg1_msg2_eph_stat_share #cs entr is rs method
  = admit()

let lemma_integration_msg1_msg2_consistence #cs entr is rs method
  = lemma_integration_msg1_msg2_eph_stat_share #cs entr is rs method;
  ()


let bundle_msg1_msg2 #cs entr is rs method
  = match (initiator_send_msg1 cs method entr is) with
        | Fail e -> Fail e
        | Res (msg1, is', hs_i') -> (
          match (responder_process_msg1 #cs rs msg1) with
            | Fail e -> Fail e
            | Res (hs_r') -> (
              lemma_responder_process_msg1_agreement #cs rs msg1;
              assert(
                post_hs_after_msg1 #cs hs_i' hs_r'
                /\ hs_r'.method = method
                /\ lbytes_eq msg1.g_x (Some?.v is'.eph_ec_keypair).pub
              );
              
              
              match (responder_send_msg2 #cs entr rs hs_r') with
                | Fail e -> Fail e
                | Res (ptx2_r, msg2, rs', hs_r'') -> (

                  match (initiator_process_msg2 #cs is' hs_i' msg2) with
                    | Fail e -> Fail e
                    | Res (ptx2_i, hs_i'') -> (
                      Res (
                        ptx2_i, ptx2_r, msg2, is', rs', hs_i'', hs_r''
                      )
                    )
                )
            )
        )

/// --------------------------
/// Initiator send Msg3 lemmas
/// --------------------------
let lemma_initiator_send_msg3_respond #cs entr is hs ptx2
  = ()

let lemma_initiator_send_msg3_consistence #cs entr is hs ptx2
  = lemma_initiator_send_msg3_respond entr is hs ptx2;
  ()


/// -----------------------------
/// Responder process Msg3 lemmas
/// -----------------------------
let lemma_responder_process_msg3_respond #cs rs hs ptx2 msg3
  = ()

let lemma_responder_process_msg3_consistence #cs rs hs ptx2 msg3
  = lemma_responder_process_msg3_respond #cs rs hs ptx2 msg3;
  ()

/// ---------------------------------------
/// Integration Msg1, Msg2, and Msg3 lemmas
/// ---------------------------------------
let bundle_msg1_msg3 #cs entr is rs method
  = match (bundle_msg1_msg2 #cs entr is rs method) with
      | Fail e -> Fail e
      | Res (ptx2_i, ptx2_r, msg2, is', rs', hs_i'', hs_r'') -> (
        match (initiator_send_msg3 #cs entr is' hs_i'' ptx2_i) with
          | Fail e -> Fail e
          | Res (msg3, hs_i''') -> (
            assert(normalize_term ptx2_i == normalize_term ptx2_r);

            match (responder_process_msg3 #cs rs' hs_r'' ptx2_r msg3) with
              | Fail e -> Fail e
              | Res (hs_r''') -> (
                // The below could be proved if ptx2_r == ptx2_i is proved in
                // integration_msg1_msg2 lemma
                assert(post_ps_unchanged_fixed_vals rs rs');
                assert(post_ps_unchanged_fixed_vals is is');


                // True
                // post_hs_after_msg3 hs_i''' hs_r'''
                assert(valid_hs_msg2_to_msg3 hs_i'' hs_i''');
                assert(valid_hs_msg2_to_msg3 hs_r'' hs_r''');

                assert(lbytes_eq (Some?.v hs_i'''.th3) (Some?.v hs_r'''.th3));
                // assert(lbytes_eq (Some?.v hs_i'''.prk4e3m) (Some?.v hs_r'''.prk4e3m));
                
                Res (is', rs', hs_i''', hs_r''')
              )
          )
      )

let lemma_integration_msg1_msg3_eph_stat_share #cs entr is rs method
  = admit()
