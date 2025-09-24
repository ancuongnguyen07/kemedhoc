module Impl.KEMEDHOC.Core.Msg3.Aux

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

module FBytes = FStar.Bytes

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
open Impl.KEMEDHOC.Core.Utilities
open Spec.KEMEDHOC.Base.Definitions

module AuxMsg2 = Impl.KEMEDHOC.Core.Msg2.Aux

(*------------------ Utilities*)
/// Should be moved later to a separate module
let handshake_state_m_disjoint_to_p3 (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (p3: plaintext3 kcs)
  = B.all_disjoint [
    // handshake_state fields
    loc hs.suite_i; loc hs.msg1_hash;
    loc hs.k_xy.is_some; loc hs.k_xy.value;
    loc hs.k_auth_R;
    loc hs.k_auth_I.is_some; loc hs.k_auth_I.value;
    loc hs.th1;
    loc hs.th2.is_some; loc hs.th2.value;
    loc hs.th3.is_some; loc hs.th3.value;
    loc hs.th4.is_some; loc hs.th4.value;
    loc hs.prk1e;
    loc hs.prk2e.is_some; loc hs.prk2e.value;
    loc hs.prk3e2m.is_some; loc hs.prk3e2m.value;
    loc hs.prk4e3m.is_some; loc hs.prk4e3m.value;
    loc hs.prk_out.is_some; loc hs.prk_out.value;
    loc hs.prk_exporter.is_some; loc hs.prk_exporter.value;
    loc hs.remote_id_cred.is_some; loc hs.remote_id_cred.value;

    // plaintext3 fields
    loc p3.id_cred_I; loc p3.mac3
  ]

let party_state_disjoint_to_p3 (#kcs: supportedKemCipherSuite)
  (ps: party_state_m kcs) (p3: plaintext3 kcs)
  = B.all_disjoint [
    // party_state fields
    loc ps.suite; loc (fst ps.static_kem_kp);
    loc (snd ps.static_kem_kp);
    loc ps.id_cred;
    loc ps.eph_kem_priv_key.is_some; loc ps.eph_kem_priv_key.value;
    loc ps.remote_static_kem_pub_key; loc ps.remote_id_cred;

    // plaintext3 fields
    loc p3.id_cred_I; loc p3.mac3
  ]

let plaintext3_disjoint_to_plaintex2 (#kcs: supportedKemCipherSuite)
  (p3: plaintext3 kcs) (p2: plaintext2 kcs)
  = B.all_disjoint [
    // plaintext3 fields
    loc p3.id_cred_I; loc p3.mac3;

    // plaintext 2 fields
    loc p2.c_R; loc p2.id_cred_R;
    loc p2.cred_R; loc p2.mac2
  ]

(*------------------ Responder's side*)


#push-options "--z3refresh --z3rlimit 200 --max_fuel 2 --max_ifuel 1"

let responder_process_msg3_check_mac3 (#kcs: supportedKemCipherSuite)
  (rs: party_state_m kcs) (hs: handshake_state_m kcs)
  (p3: plaintext3 kcs) (mac3_buff: mac23_buff kcs) (cred_I: cred_buffer)
  : ST.Stack c_response
  (ensures fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_party_state_m h0 rs
    /\ is_valid_plaintext3 h0 p3
    /\ live h0 mac3_buff /\ live h0 cred_I

    // /\ lbufferOpt_is_Some h0 hs.th3
    // /\ lbufferOpt_is_Some h0 hs.prk4e3m

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs rs
    /\ handshake_state_m_disjoint_to_p3 hs p3
    /\ handshake_state_m_disjoint_to_lbuffer hs mac3_buff
    /\ party_state_disjoint_to_p3 rs p3
    /\ party_state_disjoint_to_lbuffer rs mac3_buff
    /\ plaintext3_disjoint_to_lbuffer p3 mac3_buff
    /\ handshake_state_m_disjoint_to_lbuffer hs cred_I
    /\ party_state_disjoint_to_lbuffer rs cred_I
    /\ plaintext3_disjoint_to_lbuffer p3 cred_I
    /\ disjoint mac3_buff cred_I
  )
  (requires fun h0 res h1 ->
    let modified_locs = lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
              |+| lbufferOpt_loc hs.prk_exporter in

    (match res with
      | TypeEdhoc.CIntegrityCheckFailed -> modifies0 h0 h1
      | TypeEdhoc.CSuccess -> (
        modifies modified_locs h0 h1
        /\ lbufferOpt_is_Some h1 hs.th4 /\ lbufferOpt_is_Some h1 hs.prk_out
        /\ lbufferOpt_is_Some h1 hs.prk_exporter
      )
      | _ -> False
    )
    /\ is_valid_handshake_state_m h1 hs
    /\ is_valid_party_state_m h1 rs
    /\ is_valid_plaintext3 h1 p3
  )
  = (**) let h0 = ST.get () in

  let final_res = match (check_mac mac3_buff p3.mac3) with
    | TypeEdhoc.CIntegrityCheckFailed -> TypeEdhoc.CIntegrityCheckFailed
    | TypeEdhoc.CSuccess -> (
      // compute th4
      compute_th4 #kcs hs.th3.value p3 cred_I hs.th4.value;
      lbufferOpt_set_Some hs.th4; // set TH4 as Some

      // derive PRK_OUT
      expand_prk_out #kcs hs.prk4e3m.value hs.th4.value hs.prk_out.value;
      lbufferOpt_set_Some hs.prk_out; // set PRK_OUT as Some

      // derive PRK_EXPORTER
      expand_prk_exporter #kcs hs.prk_out.value hs.prk_exporter.value;
      lbufferOpt_set_Some hs.prk_exporter; // set PRK_EXPORTER as Some

      TypeEdhoc.CSuccess
    ) in

  (**) let h_final = ST.get () in
  final_res


val responder_process_msg3_decrypt_msg3_uti:
  #kcs: supportedKemCipherSuite
  -> rs: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> p3: plaintext3 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_party_state_m h0 rs
    /\ is_valid_plaintext3 h0 p3

    // /\ lbufferOpt_is_Some h0 hs.k_auth_I
    // /\ lbufferOpt_is_Some h0 hs.th3

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs rs
    /\ handshake_state_m_disjoint_to_p3 hs p3
    /\ party_state_disjoint_to_p3 rs p3
  )
  (ensures fun h0 res h1 ->
    let base_modified_locs = lbufferOpt_loc hs.prk4e3m in

    // True
    (match res with
      | TypeEdhoc.CIntegrityCheckFailed -> (
        modifies base_modified_locs h0 h1
        /\ lbufferOpt_is_Some h1 hs.prk4e3m
      )
      | TypeEdhoc.CSuccess -> (
        let modified_locs = base_modified_locs
                |+| lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
                |+| lbufferOpt_loc hs.prk_exporter in

        modifies modified_locs h0 h1
        /\ lbufferOpt_is_Some h1 hs.prk4e3m
        /\ lbufferOpt_is_Some h1 hs.th4 /\ lbufferOpt_is_Some h1 hs.prk_out
        /\ lbufferOpt_is_Some h1 hs.prk_exporter
      )
      | _ -> False
    )
  )


let responder_process_msg3_decrypt_msg3_uti #kcs rs hs p3
  = (**) let h0 = ST.get () in
  ST.push_frame();

  // derive salt4e3m
  let salt4e3m = create (hash_size_t kcs) (u8 0) in
  expand_salt #kcs SpecKS.info_label_salt4e3m hs.prk3e2m.value hs.th3.value salt4e3m;
  (**) let h1 = ST.get () in

  // derive PRK4e3m
  extract_prk4e3m #kcs salt4e3m hs.k_auth_I.value hs.prk4e3m.value;
  lbufferOpt_set_Some hs.prk4e3m; // set PRK4e3m as Some
  (**) let h2 = ST.get () in
  (**) assert(
    lbufferOpt_is_Some h2 hs.prk4e3m
    /\ modifies (lbufferOpt_loc hs.prk4e3m) h1 h2
  );

  // construct context3
  let cred_I = create (size SpecParser.cred_size) (u8 0) in
  copy cred_I p3.id_cred_I;

  let ctx3: context3 kcs = {
    id_cred_i = p3.id_cred_I;
    th3 = hs.th3.value;
    cred_i = cred_I;
  } in
  
  // derive MAC3
  let mac3 = create (size (SpecCrypto.mac23_size kcs)) (u8 0) in
  expand_mac3 #kcs hs.prk4e3m.value ctx3 mac3;
  (**) let h3 = ST.get () in
  (**) assert(
    is_valid_handshake_state_m h3 hs
    /\ is_valid_party_state_m h3 rs
    /\ is_valid_plaintext3 h3 p3
    /\ live h3 mac3 /\ live h3 cred_I

    // /\ lbufferOpt_is_Some h3 hs.th3
    // /\ lbufferOpt_is_Some h3 hs.prk4e3m

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs rs
    /\ handshake_state_m_disjoint_to_p3 hs p3
    /\ handshake_state_m_disjoint_to_lbuffer hs mac3
    /\ party_state_disjoint_to_p3 rs p3
    /\ party_state_disjoint_to_lbuffer rs mac3
    /\ plaintext3_disjoint_to_lbuffer p3 mac3
    /\ handshake_state_m_disjoint_to_lbuffer hs cred_I
    /\ party_state_disjoint_to_lbuffer rs cred_I
    /\ plaintext3_disjoint_to_lbuffer p3 cred_I
    /\ disjoint mac3 cred_I
  );

  // check MAC3
  let final_res = responder_process_msg3_check_mac3 #kcs rs hs p3 mac3 cred_I in
  (**) let h4 = ST.get () in
  (**) assert(
    match final_res with
      | TypeEdhoc.CIntegrityCheckFailed -> modifies0 h3 h4
      | TypeEdhoc.CSuccess -> (
        modifies (lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
                |+| lbufferOpt_loc hs.prk_exporter) h3 h4
        
        /\ lbufferOpt_is_Some h4 hs.th4
        /\ lbufferOpt_is_Some h4 hs.prk_out
        /\ lbufferOpt_is_Some h4 hs.prk_exporter
      )
      | _ -> False
  );

  ST.pop_frame();
  (**) let h_final = ST.get () in
  (**) assert(
    match final_res with
      | TypeEdhoc.CIntegrityCheckFailed -> (
        modifies (lbufferOpt_loc hs.prk4e3m) h0 h_final
        /\ lbufferOpt_is_Some h_final hs.prk4e3m
      )
      | TypeEdhoc.CSuccess -> (
        let modified_locs = (lbufferOpt_loc hs.prk4e3m)
                |+| lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
                |+| lbufferOpt_loc hs.prk_exporter in

        modifies modified_locs h0 h_final
        /\ lbufferOpt_is_Some h_final hs.prk4e3m
        /\ lbufferOpt_is_Some h_final hs.th4 /\ lbufferOpt_is_Some h_final hs.prk_out
        /\ lbufferOpt_is_Some h_final hs.prk_exporter
      )
  );

  final_res


#pop-options


(*------------------ Initiator's side*)

val initiator_send_msg3_construct_msg3:
  #kcs: supportedKemCipherSuite
  -> is: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> msg3: message3 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_party_state_eph_est_m h0 is
    // /\ is_valid_handshake_state_m_after_msg2 h0 hs
    /\ live h0 msg3

    /\ lbufferOpt_is_Some h0 hs.prk4e3m /\ lbufferOpt_is_Some h0 hs.th3

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_lbuffer hs msg3
    /\ party_state_disjoint_to_lbuffer is msg3
  )
  (ensures fun h0 res h1 ->
    match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CSuccess -> (
        let modified_locs = lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
                  |+| lbufferOpt_loc hs.prk_exporter
                  |+| loc msg3 in

        modifies modified_locs h0 h1
        /\ lbufferOpt_is_Some h1 hs.th4 /\ lbufferOpt_is_Some h1 hs.prk_out
        /\ lbufferOpt_is_Some h1 hs.prk_exporter
        // /\ is_valid_handshake_state_m_after_msg3 h1 hs
      )
      | _ -> False
  )

#push-options "--z3refresh --z3rlimit 50 --max_fuel 2 --max_ifuel 2"
let initiator_send_msg3_construct_msg3 #kcs is hs msg3
  = (**) let h0 = ST.get () in
  ST.push_frame();

  // create a buffer for credential R payload
  // in real world, the credential payload should be stored
  // locally in the communing party.
  let cred_I = create (size SpecParser.cred_size) (u8 0) in
  copy cred_I is.id_cred;

  // construct context3
  let ctx3: context3 kcs = {
    id_cred_i = is.id_cred;
    th3 = hs.th3.value;
    cred_i = cred_I;
  } in

  // derive MAC3
  let mac3 = create (size (SpecCrypto.mac23_size kcs)) (u8 0) in
  expand_mac3 #kcs hs.prk4e3m.value ctx3 mac3;

  // construct plaintext3
  let p3: plaintext3 kcs = {
    id_cred_I = is.id_cred;
    mac3 = mac3;
  } in

  // encrypt plaintext3
  let final_res = match (encrypt_plaintext3 #kcs p3 hs.th3.value hs.prk3e2m.value msg3) with
    | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
    | TypeEdhoc.CSuccess -> (
      // compute TH4
      compute_th4 #kcs hs.th3.value p3 cred_I hs.th4.value;
      lbufferOpt_set_Some hs.th4; // set TH4 as Some

      // derive PRK_OUT
      expand_prk_out #kcs hs.prk4e3m.value hs.th4.value hs.prk_out.value;
      lbufferOpt_set_Some hs.prk_out; // set PRK_OUT as Some

      // derive PRK_EXPORTER
      expand_prk_exporter #kcs hs.prk_out.value hs.prk_exporter.value;
      lbufferOpt_set_Some hs.prk_exporter; // set PRK_EXPORTER as Some

      TypeEdhoc.CSuccess
    ) in


  ST.pop_frame();
  (**) let h_final = ST.get () in
  (**) assert(
    match final_res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h_final
      | TypeEdhoc.CSuccess -> (
        let modified_locs = lbufferOpt_loc hs.th4 |+| lbufferOpt_loc hs.prk_out
                  |+| lbufferOpt_loc hs.prk_exporter
                  |+| loc msg3 in

        modifies modified_locs h0 h_final
        /\ lbufferOpt_is_Some h_final hs.th4 /\ lbufferOpt_is_Some h_final hs.prk_out
        /\ lbufferOpt_is_Some h_final hs.prk_exporter
        // /\ is_valid_handshake_state_m_after_msg3 h_final hs
      )
  );

  final_res

#pop-options


val initiator_send_msg3_set_up:
  #kcs: supportedKemCipherSuite
  -> is: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> p2: plaintext2 kcs
  -> ST.Stack unit
  (requires fun h0 ->
    is_party_state_eph_est_m h0 is
    /\ is_valid_handshake_state_m h0 hs
    // /\ is_valid_handshake_state_m_after_msg2 h0 hs
    /\ is_valid_plaintext2 h0 p2

    /\ lbufferOpt_is_Some h0 hs.th2 /\ lbufferOpt_is_Some h0 hs.prk3e2m
    /\ lbufferOpt_is_Some h0 hs.k_auth_I

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ AuxMsg2.handshake_state_m_disjoint_to_p2 hs p2
    /\ AuxMsg2.party_state_disjoint_to_p2 is p2
  )
  (ensures fun h0 _ h1 ->
    let modified_locs = lbufferOpt_loc hs.th3 |+| lbufferOpt_loc hs.prk4e3m in

    modifies modified_locs h0 h1
    // As the two below fields are Some, directly conflicts the post-condition
    // `is_valid_handshake_state_m_after_msg2` where the two fields should
    // be None.
    /\ lbufferOpt_is_Some h1 hs.th3 /\ lbufferOpt_is_Some h1 hs.prk4e3m
    /\ is_valid_handshake_state_m h1 hs
    /\ is_party_state_eph_est_m h1 is
    /\ is_valid_plaintext2 h1 p2
  )

#push-options "--z3refresh --z3rlimit 80 --max_fuel 2 --max_ifuel 2"
let initiator_send_msg3_set_up #kcs is hs p2
  = (**) let h0 = ST.get () in
  ST.push_frame();
  
  // create a buffer for credential R payload
  // in real world, the credential payload should be stored
  // locally in the communing party.
  let cred_R = create (size SpecParser.cred_size) (u8 0) in
  copy cred_R p2.id_cred_R;

  // derive TH3
  compute_th3 #kcs hs.th2.value p2 cred_R hs.th3.value;
  lbufferOpt_set_Some hs.th3; // set TH3 as Some

  // derive SALT4e3m
  let salt4e3m = create (hash_size_t kcs) (u8 0) in
  expand_salt #kcs SpecKS.info_label_salt4e3m hs.prk3e2m.value hs.th3.value salt4e3m;

  // derive PRK4e3m
  extract_prk4e3m #kcs salt4e3m hs.k_auth_I.value hs.prk4e3m.value;
  lbufferOpt_set_Some hs.prk4e3m; // set PRK4e3m as Some

  ST.pop_frame();
  (**) let h_final =  ST.get() in
  (**) assert(
    let modified_locs = lbufferOpt_loc hs.th3 |+| lbufferOpt_loc hs.prk4e3m in

    modifies modified_locs h0 h_final
    // As the two below fields are Some, directly conflicts the post-condition
    // `is_valid_handshake_state_m_after_msg2` where the two fields should
    // be None.
    /\ lbufferOpt_is_Some h_final hs.th3 /\ lbufferOpt_is_Some h_final hs.prk4e3m
    /\ is_valid_handshake_state_m h_final hs
    /\ is_party_state_eph_est_m h_final is
    /\ is_valid_plaintext2 h_final p2
  )

#pop-options
