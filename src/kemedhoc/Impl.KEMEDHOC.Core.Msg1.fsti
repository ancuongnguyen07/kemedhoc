module Impl.KEMEDHOC.Core.Msg1

(*LowStar related modules*)
open Lib.ByteBuffer
open Lib.IntTypes
open Lib.Buffer

(*HACL Random lib*)
open Lib.RandomBuffer.System

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module Spec = Spec.KEMEDHOC.Core

module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecParser = Spec.KEMEDHOC.Parser

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
        // let modified_locs = ( loc entropy_p |+| loc msg1.c_i
        //     |+| loc msg1.pk_x |+| loc is.eph_kem_priv_key.value
        //     |+| loc kem_state
        //     |+| loc is.eph_kem_priv_key.is_some
        //     |+| loc msg1.ct_auth_R |+| loc hs.k_auth_R
        //     |+| loc hs.th1
        //     |+| loc hs.prk1e
        //     |+| loc msg1.c1 |+| loc msg1.method |+| loc msg1.suite_i
        //     |+| loc hs.msg1_hash
        // ) in

        // modifies modified_locs h0 h1
        True
      )
      | _ -> False
  )