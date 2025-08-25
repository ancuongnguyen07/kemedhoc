module Spec.KEMEDHOC.Core.Lemmas

friend Spec.KEMEDHOC.Core

/// Lemmas for sending/processing message1
let lemma_initiator_send_msg1_post_cond kcs is entr
  = ()

let lemma_responder_process_msg1_return kcs rs msg1
  = ()

let lemma_bundle_msg1_correctness kcs is rs entr
  = ()

/// Lemmas for sending/processing message2
let lemma_responder_send_msg2_always_res kcs rs hs msg1 entr
  = ()

let lemma_initiator_process_msg2_response kcs is hs msg2
  = ()

/// Lemma for bundle msg1/2
let lemma_bundle_msg1_msg2_correctness kcs is rs entr
  = ()

/// Lemmas for bundle message1/2/3
let lemma_bundle_msg1_msg2_msg3_correctness kcs is rs entr
  = ()