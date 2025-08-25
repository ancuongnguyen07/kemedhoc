module Spec.KEMEDHOC.Core.Lemmas

module Seq = Lib.Sequence
open Lib.RandomSequence

open Spec.KEMEDHOC.CryptoPrimitives
open Spec.KEMEDHOC.Parser
open Spec.KEMEDHOC.Base.Definitions

open Spec.KEMEDHOC.Core

/// Lemmas for sending/processing message1
val lemma_initiator_send_msg1_post_cond:
  kcs: supportedKemCipherSuite
  -> is: party_state #kcs
  -> entr: entropy
  -> Lemma (ensures (
    match (initiator_send_msg1 kcs is entr) with
      | Fail _ -> false
      | Res (msg1, is', hs) -> (
        Some? is'.eph_kem_priv_key
      )
  ))
  [SMTPat (initiator_send_msg1 kcs is entr)]

val lemma_responder_process_msg1_return:
  kcs: supportedKemCipherSuite
  -> rs: party_state #kcs
  -> msg1: message1 #kcs
  -> Lemma (ensures (
    match (responder_process_msg1 kcs rs msg1) with
      | Fail DecryptionFailed | Fail InvalidCredential -> True
      | Res (hs', ptx1) -> (
        Option.isSome hs'.remote_id_cred
        /\ Seq.equal (Some?.v hs'.remote_id_cred) ptx1.id_cred_I
      ) 
      | Fail _ -> False
  ))
  [SMTPat (responder_process_msg1 kcs rs msg1)]

/// Lemmas for bundle message1
val lemma_bundle_msg1_correctness:
  kcs: supportedKemCipherSuite
  -> is: party_state #kcs
  -> rs: party_state #kcs
  -> entr: entropy
  -> Lemma (requires (
    precond_parties_setup kcs is rs entr
  ))
  (ensures (
    match (bundle_msg1 kcs is rs entr) with
      // | Fail DecryptionFailed -> True
      // Fail InvalidCredential should be False
      // as this lemma requires precondition for parties setup
      | Fail _ -> False
      | Res (msg1, hs_i, hs_r, is', rs', decrypted_ptx1) -> (
          hs_equal hs_i hs_r
          /\ Option.isSome hs_r.remote_id_cred
          /\ Seq.equal (Some?.v hs_r.remote_id_cred) is'.id_cred
          /\ Seq.equal is.id_cred decrypted_ptx1.id_cred_I
          /\ Seq.equal is.id_cred decrypted_ptx1.cred_I
          /\ ps_equal_non_eph is is'
          /\ ps_equal_all rs rs'
        )
  ))
  [SMTPat (bundle_msg1 kcs is rs entr)]

/// Lemmas for sending/processing message2
val lemma_responder_send_msg2_always_res:
  kcs: supportedKemCipherSuite
  -> rs: party_state #kcs
  -> hs: handshake_state_init #kcs
  -> msg1: message1 #kcs
  -> entr: entropy
  -> Lemma (ensures (
    match (responder_send_msg2 kcs rs hs msg1 entr) with
      | Fail _ -> False
      | Res (msg2, hs') -> (
        valid_hs_msg1_to_msg2 hs hs'
      )
  ))
  [SMTPat (responder_send_msg2 kcs rs hs msg1 entr)]

val lemma_initiator_process_msg2_response:
  kcs: supportedKemCipherSuite
  -> is: party_state_eph_est #kcs
  -> hs: handshake_state_init #kcs
  -> msg2: message2 #kcs
  -> Lemma (ensures (
    match (initiator_process_msg2 kcs is hs msg2) with
      | Fail DecryptionFailed | Fail InvalidCredential | Fail IntegrityCheckFailed -> True
      | Fail _ -> False
      | Res (hs', ptx2) -> (
        valid_hs_msg1_to_msg2 hs hs'
      )
  ))
  [SMTPat (initiator_process_msg2 kcs is hs msg2)]

/// Lemma for bundle message1/2
val lemma_bundle_msg1_msg2_correctness:
  kcs: supportedKemCipherSuite
  -> is: party_state #kcs
  -> rs: party_state #kcs
  -> entr: entropy
  -> Lemma (requires (
    precond_parties_setup kcs is rs entr
  ))
  (ensures (
    match (bundle_msg1_msg2 kcs is rs entr) with
      // | Fail DecryptionFailed -> True
      // Fail InvalidCredential should be False
      // as this lemma requires precondition for parties setup
      | Fail _ -> False
      | Res (msg2, hs_i'', hs_r'', is', rs', decrypted_ptx2) -> (
          hs_equal hs_i'' hs_r''
          /\ Seq.equal rs.id_cred decrypted_ptx2.id_cred_R
          /\ Seq.equal rs.id_cred decrypted_ptx2.cred_R
          /\ ps_equal_non_eph is is'
          /\ ps_equal_all rs rs'
        )
  ))
  [SMTPat (bundle_msg1_msg2 kcs is rs entr)]

/// Lemmas for bundle message1/2/3
val lemma_bundle_msg1_msg2_msg3_correctness:
  kcs: supportedKemCipherSuite
  -> is: party_state #kcs
  -> rs: party_state #kcs
  -> entr: entropy
  -> Lemma (requires (
    precond_parties_setup kcs is rs entr
  ))
  (ensures (
    match (bundle_msg1_msg2_msg3 kcs is rs entr) with
      // | Fail DecryptionFailed -> True
      // Fail InvalidCredential should be False
      // as this lemma requires precondition for parties setup
      | Fail _ -> False
      | Res (msg3, hs_i''', hs_r''', is', rs', ptx3) -> (
          hs_equal hs_i''' hs_r'''
          /\ Seq.equal is.id_cred ptx3.id_cred_I
          /\ ps_equal_non_eph is is'
          /\ ps_equal_all rs rs'
        )
  ))
  [SMTPat (bundle_msg1_msg2_msg3 kcs is rs entr)]