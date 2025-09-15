module Impl.KEMEDHOC.Core.Msg1

(*LowStar related modules*)
open Lib.ByteBuffer
open Lib.IntTypes
open Lib.Buffer

(*HACL Random lib*)
open Lib.RandomBuffer.System
module HACLRandom = Lib.RandomSequence

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module Spec = Spec.KEMEDHOC.Core

module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecParser = Spec.KEMEDHOC.Parser
module SpecTH = Spec.KEMEDHOC.TranscriptHash
module SpecKS = Spec.KEMEDHOC.KeySchedule

module SpecEdhocSerd = Spec.EDHOC.Serialization

module TypeEdhoc = TypeHelper.EDHOC

(*EDHOC utilities*)
open Impl.EDHOC.Utilities

(*KEMEDHOC utilities*)
open Impl.KEMEDHOC.Types
open Impl.KEMEDHOC.CryptoPrimitives
open Impl.KEMEDHOC.KeySchedule
open Impl.KEMEDHOC.Parser
open Impl.KEMEDHOC.Ciphertext
open Impl.KEMEDHOC.TranscriptHash
open Impl.KEMEDHOC.Core
open Spec.KEMEDHOC.Base.Definitions

(*------------------ Message 1*)
val responder_process_msg1:
  kcs: supportedKemCipherSuite
  -> rs: party_state_m kcs
  -> msg1: message1 kcs
  -> hs: handshake_state_m kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_party_state_m h0 rs /\ live h0 entropy_p /\ live h0 kem_state
    /\ is_valid_message1 h0 msg1
    /\ is_legit_message1 h0 msg1 /\ is_valid_handshake_state_m h0 hs
    
    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs rs
    /\ handshake_state_m_disjoint_to_lbuffer hs kem_state
    /\ handshake_state_m_disjoint_to_lbuffer hs entropy_p
    /\ handshake_state_m_disjoint_to_msg1 hs msg1
    /\ party_state_disjoint_to_lbuffer rs kem_state
    /\ party_state_disjoint_to_lbuffer rs entropy_p
    /\ party_state_disjoint_to_msg1 rs msg1
    /\ message1_disjoint_to_lbuffer msg1 kem_state
    /\ message1_disjoint_to_lbuffer msg1 entropy_p
    /\ disjoint kem_state entropy_p
  )
  (ensures fun h0 res h1 ->
    True
  )

/// Initiator's side
noextract
val initiator_set_up_msg1:
  kcs: supportedKemCipherSuite
  -> is: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> msg1: message1 kcs
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_party_state_m h0 is /\ live h0 entropy_p /\ live h0 kem_state
    /\ is_valid_handshake_state_m h0 hs
    /\ is_valid_message1 h0 msg1
    
    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_lbuffer hs kem_state
    /\ handshake_state_m_disjoint_to_lbuffer hs entropy_p
    /\ handshake_state_m_disjoint_to_msg1 hs msg1
    /\ party_state_disjoint_to_lbuffer is kem_state
    /\ party_state_disjoint_to_lbuffer is entropy_p
    /\ party_state_disjoint_to_msg1 is msg1
    /\ message1_disjoint_to_lbuffer msg1 kem_state
    /\ message1_disjoint_to_lbuffer msg1 entropy_p
    /\ disjoint kem_state entropy_p

  )
  (ensures fun h0 _ h1 ->
    let modified_locs = loc entropy_p |+| loc msg1.c_i
            |+| loc msg1.pk_x |+| loc is.eph_kem_priv_key.value |+| loc kem_state
            |+| loc is.eph_kem_priv_key.is_some
            |+| loc msg1.ct_auth_R |+| loc hs.k_auth_R
            |+| loc hs.th1
            |+| loc hs.prk1e in
    // /// Specification
    // let entr = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
    // // generate connection ID C_I
    // let c_i = HACLRandom.unsound_crypto_random2 SpecParser.c_id_size in
    // // generate ephemeral KEM keypair
    // let pk_x, sk_x = SpecCrypto.kem_keygen kcs entr in
    // // lemma_kem_functional_correctness kcs entr;
    // // encap the Responder's static public KEM key for authentication
    // let ct_auth_R, k_auth_R = SpecCrypto.kem_encaps kcs entr (is.remote_static_kem_pub_key) in
    // // compute TH1
    // let th1 = SpecTH.compute_th1 #kcs pk_x ct_auth_R in
    // // derive PRK1e
    // let prk1e = SpecKS.extract_prk1e th1 k_auth_R in

    modifies modified_locs h0 h1
    /\ is_valid_handshake_state_m h1 hs
    /\ is_valid_party_state_m h1 is
    /\ is_valid_message1 h1 msg1
    // /\ (
    //   let msg1_s = message1_eval h1 msg1 in
    //   let hs_s = handshake_state_m_eval h1 hs in
    //   let is_s = party_state_m_eval h1 is in

    //   Seq.equal msg1_s.c_i c_i
    //   /\ Seq.equal msg1_s.pk_x pk_x
    //   /\ Some? is_s.eph_kem_priv_key /\ Seq.equal (Some?.v is_s.eph_kem_priv_key) sk_x
    //   /\ Seq.equal msg1_s.ct_auth_R ct_auth_R /\ Seq.equal hs_s.k_auth_R k_auth_R
    //   /\ Seq.equal hs_s.th1 th1 /\ Seq.equal hs_s.prk1e prk1e
    // )
  )

val initiator_construct_msg1:
  kcs: supportedKemCipherSuite
  -> is: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> msg1: message1 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_party_state_m h0 is
    /\ is_valid_handshake_state_m h0 hs
    /\ is_valid_message1 h0 msg1
    
    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_msg1 hs msg1
    /\ party_state_disjoint_to_msg1 is msg1
  )
  (ensures fun h0 res h1 ->
    match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CSuccess -> (
        let modified_locs = loc msg1.c1 |+| loc msg1.method |+| loc msg1.suite_i
            |+| loc hs.msg1_hash in

        modifies modified_locs h0 h1
        /\ is_valid_handshake_state_m h1 hs
        /\ is_valid_party_state_m h1 is
        /\ is_valid_message1 h1 msg1 /\ is_legit_message1 h1 msg1
      )
      | _ -> False
  )

val initiator_send_msg1:
  kcs: supportedKemCipherSuite
  -> is: party_state_m kcs
  -> msg1: message1 kcs
  -> hs: handshake_state_m kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_party_state_m h0 is /\ live h0 entropy_p /\ live h0 kem_state
    /\ is_valid_handshake_state_m h0 hs /\ is_valid_message1 h0 msg1
    
    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_lbuffer hs kem_state
    /\ handshake_state_m_disjoint_to_lbuffer hs entropy_p
    /\ handshake_state_m_disjoint_to_msg1 hs msg1
    /\ party_state_disjoint_to_lbuffer is kem_state
    /\ party_state_disjoint_to_lbuffer is entropy_p
    /\ party_state_disjoint_to_msg1 is msg1
    /\ message1_disjoint_to_lbuffer msg1 kem_state
    /\ message1_disjoint_to_lbuffer msg1 entropy_p
    /\ disjoint kem_state entropy_p

  )
  (ensures fun h0 res h1 ->
    match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> (
        modifies (loc entropy_p |+| loc msg1.c_i
            |+| loc msg1.pk_x |+| loc is.eph_kem_priv_key.value
            |+| loc kem_state
            |+| loc is.eph_kem_priv_key.is_some
            |+| loc msg1.ct_auth_R |+| loc hs.k_auth_R
            |+| loc hs.th1
            |+| loc hs.prk1e) h0 h1
      )
      | TypeEdhoc.CSuccess -> (
        let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
        match (Spec.initiator_send_msg1 kcs (party_state_m_eval h0 is) e0_v) with
          | Fail _ -> False
          | Res (msg1_s, is_s, hs_s) -> (
            let modified_locs = loc entropy_p |+| loc msg1.c_i
            |+| loc msg1.pk_x |+| loc is.eph_kem_priv_key.value
            |+| loc kem_state
            |+| loc is.eph_kem_priv_key.is_some
            |+| loc msg1.ct_auth_R |+| loc hs.k_auth_R
            |+| loc hs.th1
            |+| loc hs.prk1e
            |+| loc msg1.c1 |+| loc msg1.method |+| loc msg1.suite_i
            |+| loc hs.msg1_hash in

            is_valid_handshake_state_m h1 hs
            /\ is_valid_party_state_m h1 is
            /\ is_valid_message1 h1 msg1 /\ is_legit_message1 h1 msg1
            /\ Spec.hs_equal (handshake_state_m_eval h1 hs) hs_s
            /\ Spec.ps_equal_all (party_state_m_eval h1 is) is_s
            /\ SpecParser.message1_equal (message1_eval h1 msg1) msg1_s
            /\ modifies (modified_locs) h0 h1
          )
      )
      | _ -> False
  )