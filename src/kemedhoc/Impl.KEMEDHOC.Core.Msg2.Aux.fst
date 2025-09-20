module Impl.KEMEDHOC.Core.Msg2.Aux

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

(*-------------- Utilities*)
inline_for_extraction noextract
let lbufferOpt_get_value (#len: size_t)
  (buff: lbufferOpt len)
  : lbuffer uint8 len
  = buff.value

/// Disjoint to Context 2
let handshake_state_m_disjoint_to_context2 (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (ctx2: context2 kcs)
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

    // context 2 fields
    loc ctx2.c_r; loc ctx2.id_cred_r; loc ctx2.cred_r;
    loc ctx2.th2
  ]

/// Disjoint to Plaintext 2
let handshake_state_m_disjoint_to_p2 (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (p2: plaintext2 kcs)
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

    // plaintext 2 fieldds
    loc p2.c_R; loc p2.id_cred_R;
    loc p2.cred_R; loc p2.mac2
  ]

let party_state_disjoint_to_p2 (#kcs: supportedKemCipherSuite)
  (ps: party_state_m kcs) (p2: plaintext2 kcs)
  = B.all_disjoint [
    // party_state fields
    loc ps.suite; loc (fst ps.static_kem_kp);
    loc (snd ps.static_kem_kp);
    loc ps.id_cred;
    loc ps.eph_kem_priv_key.is_some; loc ps.eph_kem_priv_key.value;
    loc ps.remote_static_kem_pub_key; loc ps.remote_id_cred;

    // message 2 fields
    loc p2.c_R; loc p2.id_cred_R;
    loc p2.cred_R; loc p2.mac2
  ]

/// Disjoint to Message 2
let handshake_state_m_disjoint_to_msg2 (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (msg2: message2 kcs)
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

    // message 2 fields
    loc msg2.ct_y; loc msg2.ct_auth_I;
    loc msg2.c2
  ]

let party_state_disjoint_to_msg2 (#kcs: supportedKemCipherSuite)
  (ps: party_state_m kcs) (msg2: message2 kcs)
  = B.all_disjoint [
    // party_state fields
    loc ps.suite; loc (fst ps.static_kem_kp);
    loc (snd ps.static_kem_kp);
    loc ps.id_cred;
    loc ps.eph_kem_priv_key.is_some; loc ps.eph_kem_priv_key.value;
    loc ps.remote_static_kem_pub_key; loc ps.remote_id_cred;

    // message 2 fields
    loc msg2.ct_y; loc msg2.ct_auth_I;
    loc msg2.c2
  ]

let message2_disjoint_to_p2 (#kcs: supportedKemCipherSuite)
  (msg2: message2 kcs) (p2: plaintext2 kcs)
  = B.all_disjoint [
    // message 2 fieldds
    loc msg2.ct_y; loc msg2.ct_auth_I;
    loc msg2.c2;

    // plaintext 2 fields
    loc p2.c_R; loc p2.id_cred_R;
    loc p2.cred_R; loc p2.mac2
  ]

let message2_disjoint_to_msg1 (#kcs: supportedKemCipherSuite)
  (msg2: message2 kcs) (msg1: message1 kcs)
  = B.all_disjoint [
    // message 2 fields
    loc msg2.ct_y; loc msg2.ct_auth_I;
    loc msg2.c2;

    // message 1 fields
    loc msg1.method; loc msg1.suite_i;
    loc msg1.pk_x; loc msg1.ct_auth_R;
    loc msg1.c_i; loc msg1.c1
  ]


(*----------------- Initiator's side*)
val initiator_process_msg2_set_up:
  kcs: supportedKemCipherSuite
  -> is: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> msg2: message2 kcs
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_party_state_m h0 is /\ lbufferOpt_is_Some h0 is.eph_kem_priv_key
    /\ is_valid_message2 h0 msg2

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_msg2 hs msg2
    /\ party_state_disjoint_to_msg2 is msg2
  )
  (ensures fun h0 _ h1 ->
    let modified_locs = lbufferOpt_loc hs.k_xy |+| lbufferOpt_loc hs.k_auth_I
              |+| lbufferOpt_loc hs.th2 |+| lbufferOpt_loc hs.prk2e in

    modifies modified_locs h0 h1
    /\ is_valid_handshake_state_m h1 hs
    /\ is_valid_party_state_m h1 is
    /\ is_valid_message2 h1 msg2

    /\ lbufferOpt_is_Some h1 hs.k_xy /\ lbufferOpt_is_Some h1 hs.k_auth_I
    /\ lbufferOpt_is_Some h1 hs.th2 /\ lbufferOpt_is_Some h1 hs.prk2e
  )

#push-options "--z3rlimit 30 --max_fuel 4 --max_ifuel 4"
let initiator_process_msg2_set_up kcs is hs msg2
  = (**) let h0 = ST.get () in
  // decap ct_y -> k_xy
  let sk_X = is.eph_kem_priv_key.value in
  kem_decaps kcs sk_X msg2.ct_y hs.k_xy.value;
  lbufferOpt_set_Some hs.k_xy; // set Some for k_xy
  (**) let h1 = ST.get () in
  (**) assert(modifies (lbufferOpt_loc hs.k_xy) h0 h1);

  // decap ct_auth_I -> k_auth_I
  let sk_I = snd is.static_kem_kp in
  kem_decaps kcs sk_I msg2.ct_auth_I hs.k_auth_I.value;
  lbufferOpt_set_Some hs.k_auth_I; // set Some for k_auth_I
  (**) let h2 = ST.get () in
  (**) assert(modifies (lbufferOpt_loc hs.k_xy |+| lbufferOpt_loc hs.k_auth_I) h0 h2);

  // derive TH2
  compute_th2_pre_hash #kcs msg2.ct_y hs.k_auth_I.value hs.msg1_hash hs.th2.value;
  lbufferOpt_set_Some hs.th2; // set Some for th2
  (**) let h3 = ST.get () in
  (**) assert(modifies (lbufferOpt_loc hs.k_xy |+| lbufferOpt_loc hs.k_auth_I
              |+| lbufferOpt_loc hs.th2) h0 h3);

  // derive PRK2e
  extract_prk2e #kcs hs.prk1e hs.th2.value hs.k_xy.value hs.prk2e.value;
  lbufferOpt_set_Some hs.prk2e; // set Some for prk2e
  (**) let h4 = ST.get () in
  (**) assert(modifies (lbufferOpt_loc hs.k_xy |+| lbufferOpt_loc hs.k_auth_I
              |+| lbufferOpt_loc hs.th2 |+| lbufferOpt_loc hs.prk2e) h0 h4);

  ()

#pop-options

#push-options "--z3rlimit 40"
let initiator_process_msg2_decrypt_c2_uti (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (is: party_state_m kcs)
  (ptx2: plaintext2 kcs)
  : ST.Stack c_response
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_party_state_m h0 is
    /\ is_valid_plaintext2 h0 ptx2

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_p2 hs ptx2
    /\ party_state_disjoint_to_p2 is ptx2
  )
  (ensures fun h0 res h1 ->
    modifies0 h0 h1
    /\ (match res with
        | TypeEdhoc.CInvalidCredential
        | TypeEdhoc.CIntegrityCheckFailed
        | TypeEdhoc.CSuccess -> True
        | _ -> False
    )
  )
  = ST.push_frame();
  (**) let h0 = ST.get () in

  // check credential ID
  let res = check_credential ptx2.id_cred_R is.remote_id_cred in
  let final_res = match res with
    | TypeEdhoc.CInvalidCredential -> res
    | TypeEdhoc.CSuccess -> (
      // construct context2
      let ctx2: context2 kcs = {
        c_r = ptx2.c_R;
        id_cred_r = ptx2.id_cred_R;
        th2 = hs.th2.value;
        cred_r = ptx2.cred_R;
      } in

      // derive MAC2
      let mac2 = create (size (SpecCrypto.mac23_size kcs)) (u8 0) in
      expand_mac2 #kcs hs.prk3e2m.value ctx2 mac2;
      (**) let h2 = ST.get () in

      // check MAC2
      check_mac #kcs mac2 ptx2.mac2

    ) in

  ST.pop_frame();
  final_res

#pop-options

val initiator_process_msg2_decrypt_c2:
  kcs: supportedKemCipherSuite
  -> is: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> msg2: message2 kcs
  -> ptx2: plaintext2 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_party_state_m h0 is
    /\ is_valid_message2 h0 msg2
    /\ is_valid_plaintext2 h0 ptx2

    /\ lbufferOpt_is_Some h0 hs.th2 /\ lbufferOpt_is_Some h0 hs.prk2e
    /\ lbufferOpt_is_Some h0 hs.k_auth_I /\ lbufferOpt_is_Some h0 hs.k_xy

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_msg2 hs msg2
    /\ handshake_state_m_disjoint_to_p2 hs ptx2
    /\ party_state_disjoint_to_msg2 is msg2
    /\ party_state_disjoint_to_p2 is ptx2
    /\ message2_disjoint_to_p2 msg2 ptx2
  )
  (ensures fun h0 res h1 ->
    let modified_locs = lbufferOpt_loc hs.prk3e2m
                          |+| plaintext2_union ptx2 in
    (match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
      | TypeEdhoc.CDecryptionFailure -> modifies0 h0 h1
      | TypeEdhoc.CInvalidCredential
      | TypeEdhoc.CIntegrityCheckFailed
      | TypeEdhoc.CSuccess -> (
        modifies modified_locs h0 h1
        /\ lbufferOpt_is_Some h1 hs.prk3e2m
      )
      | _ -> False  
    )
    /\ is_valid_handshake_state_m h1 hs
    /\ is_valid_party_state_m h1 is
    /\ is_valid_message2 h1 msg2
  )

#push-options "--z3refresh --z3rlimit 60 --max_fuel 2 --max_ifuel 2"
let initiator_process_msg2_decrypt_c2_set_up (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (p2: plaintext2 kcs)
  (ptx2_buffer: plaintext2_buff kcs)
  : ST.Stack unit
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_plaintext2 h0 p2
    /\ live h0 ptx2_buffer

    /\ handshake_state_m_disjoint_to_p2 hs p2
    /\ handshake_state_m_disjoint_to_lbuffer hs ptx2_buffer
    /\ B.loc_disjoint (plaintext2_union p2) (loc ptx2_buffer)
  )
  (ensures fun h0 _ h1 ->
    let modified_locs = lbufferOpt_loc hs.prk3e2m |+| plaintext2_union p2 in

    modifies modified_locs h0 h1
    /\ is_valid_handshake_state_m h1 hs
    /\ is_valid_plaintext2 h1 p2
    /\ lbufferOpt_is_Some h1 hs.prk3e2m
  )
  = ST.push_frame();
  (**) let h0 = ST.get () in

  // derive SALT3e2m
  let salt3e2m = create (hash_size_t kcs) (u8 0) in
  expand_salt #kcs SpecKS.info_label_salt3e2m hs.prk2e.value hs.th2.value salt3e2m;
  (**) let h2 = ST.get () in

  // derive PRK3e2m
  extract_prk3e2m #kcs salt3e2m hs.k_auth_R hs.prk3e2m.value;
  lbufferOpt_set_Some hs.prk3e2m; // set Some for prk3e2m
  (**) let h3 = ST.get () in

  // deserialize plaintext2
  deserialize_ptx2 kcs ptx2_buffer p2;
  (**) let h4 = ST.get () in
  (**) assert(
    let modified_locs = loc salt3e2m
                        |+| lbufferOpt_loc hs.prk3e2m
                        |+| plaintext2_union p2 in
    modifies modified_locs h0 h4
  );

  ST.pop_frame();
  (**) let h_final = ST.get () in
  ()

let initiator_process_msg2_decrypt_c2 kcs is hs msg2 ptx2
  = (**) let h0 = ST.get () in
  ST.push_frame();

  // create a buffer containing un-deserialized plaintext2
  let ptx2_buffer = create (plaintext2_size_t kcs) (u8 0) in
  let res = decrypt_ciphertext2 #kcs msg2.c2 hs.th2.value hs.prk2e.value ptx2_buffer in
  (**) let h1 = ST.get () in
  let final_res = match res with
    | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
    | TypeEdhoc.CDecryptionFailure -> res
    | TypeEdhoc.CSuccess -> (
      (**) assert(modifies1 ptx2_buffer h0 h1);
      initiator_process_msg2_decrypt_c2_set_up hs ptx2 ptx2_buffer;

      initiator_process_msg2_decrypt_c2_uti #kcs hs is ptx2
    ) in

  ST.pop_frame();
  (**) let h_final = ST.get () in
  (**) assert(res == TypeEdhoc.CSuccess ==> (
    modifies (lbufferOpt_loc hs.prk3e2m |+| plaintext2_union ptx2) h0 h_final
  ));
  final_res


#pop-options

(*----------------- Responder's side*)
val responder_send_msg2_set_up:
  kcs: supportedKemCipherSuite
  -> rs: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> msg1: message1 kcs
  -> msg2: message2 kcs
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_party_state_m h0 rs
    /\ is_valid_message1 h0 msg1 /\ is_legit_message1 h0 msg1
    /\ is_valid_message2 h0 msg2
    /\ live h0 kem_state /\ live h0 entropy_p

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs rs
    /\ handshake_state_m_disjoint_to_msg1 hs msg1
    /\ handshake_state_m_disjoint_to_msg2 hs msg2
    /\ handshake_state_m_disjoint_to_lbuffer hs kem_state
    /\ handshake_state_m_disjoint_to_lbuffer hs entropy_p
    /\ party_state_disjoint_to_msg1 rs msg1
    /\ party_state_disjoint_to_msg2 rs msg2
    /\ party_state_disjoint_to_lbuffer rs kem_state
    /\ party_state_disjoint_to_lbuffer rs entropy_p
    /\ message1_disjoint_to_lbuffer msg1 kem_state
    /\ message1_disjoint_to_lbuffer msg1 entropy_p
    /\ message2_disjoint_to_lbuffer msg2 kem_state
    /\ message2_disjoint_to_lbuffer msg2 entropy_p
    /\ message2_disjoint_to_msg1 msg2 msg1
    /\ disjoint kem_state entropy_p
  )
  (ensures fun h0 _ h1 ->
    let modified_locs
      = loc kem_state |+| loc entropy_p |+|
      lbufferOpt_loc hs.k_xy |+| loc msg2.ct_y
      |+| loc msg2.ct_auth_I |+| lbufferOpt_loc hs.k_auth_I
      |+| lbufferOpt_loc hs.th2
      |+| lbufferOpt_loc hs.prk2e |+| lbufferOpt_loc hs.prk3e2m in

    modifies modified_locs h0 h1
    /\ lbufferOpt_is_Some h1 hs.k_xy /\ lbufferOpt_is_Some h1 hs.k_auth_I
    /\ lbufferOpt_is_Some h1 hs.th2 /\ lbufferOpt_is_Some h1 hs.prk2e
    /\ lbufferOpt_is_Some h1 hs.prk3e2m
    /\ is_valid_handshake_state_m h1 hs
    /\ is_valid_party_state_m h1 rs
    /\ is_valid_message1 h0 msg1 /\ is_valid_message2 h0 msg2

  )

val responder_construct_msg2:
  kcs: supportedKemCipherSuite
  -> rs: party_state_m kcs
  -> hs: handshake_state_m kcs
  -> msg2: message2 kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_party_state_m h0 rs
    /\ is_valid_message2 h0 msg2
    /\ live h0 entropy_p

    /\ lbufferOpt_is_Some h0 hs.prk3e2m
    /\ lbufferOpt_is_Some h0 hs.th2 /\ lbufferOpt_is_Some h0 hs.prk2e

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs rs
    /\ handshake_state_m_disjoint_to_msg2 hs msg2
    /\ handshake_state_m_disjoint_to_lbuffer hs entropy_p
    /\ party_state_disjoint_to_msg2 rs msg2
    /\ party_state_disjoint_to_lbuffer rs entropy_p
    /\ message2_disjoint_to_lbuffer msg2 entropy_p
  )
  (ensures fun h0 res h1 ->
    (match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CSuccess -> modifies1 msg2.c2 h0 h1
      | _ -> False)
    /\ is_valid_handshake_state_m h1 hs
    /\ is_valid_party_state_m h1 rs
    /\ is_valid_message2 h1 msg2
  )

#push-options "--z3refresh --z3rlimit 40 --max_fuel 4 --max_ifuel 4"
let responder_construct_msg2_uti (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (ctx2: context2 kcs) (c2: c2_buff kcs)
  : ST.Stack c_response
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_context2 h0 ctx2
    /\ live h0 c2
    /\ loc ctx2.th2 == loc hs.th2.value

    // Disjointness
    /\ handshake_state_m_disjoint_to_lbuffer hs c2
    /\ B.all_disjoint [loc c2; loc ctx2.c_r; loc ctx2.id_cred_r;
                      loc ctx2.cred_r; loc ctx2.th2;
                      loc hs.prk2e.value; loc hs.prk3e2m.value]

    /\ lbufferOpt_is_Some h0 hs.prk3e2m /\ lbufferOpt_is_Some h0 hs.th2
    /\ lbufferOpt_is_Some h0 hs.prk2e
  
  )
  (ensures fun h0 res h1 ->
    match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CSuccess -> (
        modifies1 c2 h0 h1
        /\ is_valid_handshake_state_m h1 hs
        /\ is_valid_context2 h1 ctx2
      )
      | _ -> False
  )
  = ST.push_frame();
  (**) let h0 = ST.get () in 
  // derive MAC2
  let mac2: mac23_buff kcs = create (size (SpecCrypto.mac23_size kcs)) (u8 0) in
  (**) let h1 = ST.get () in
  (**) assert(is_valid_context2 h1 ctx2 /\ live h1 hs.prk3e2m.value /\ live h1 mac2
        /\ B.all_disjoint [loc hs.prk3e2m.value; loc hs.th2.value ; loc mac2]
    );
  // !!! Error in BigOps here. Do not know why
  expand_mac2 #kcs hs.prk3e2m.value ctx2 mac2;
  (**) let h2 = ST.get () in

  // construct plaintext2
  let p2: plaintext2 kcs = {
    c_R = ctx2.c_r;
    id_cred_R = ctx2.id_cred_r;
    cred_R = ctx2.cred_r;
    mac2 = mac2;
  } in

  // encrypt plaintext2
  let res = encrypt_plaintext2 #kcs p2 hs.th2.value hs.prk2e.value c2 in
  (**) let h3 = ST.get () in
  (**) assert(res == TypeEdhoc.CSuccess \/ res == TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig);
  (**) assert(match res with
      | TypeEdhoc.CSuccess -> modifies1 c2 h2 h3
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h2 h3  
  );

  ST.pop_frame();
  (**) let h_final = ST.get () in
  (**) assert(
    is_valid_handshake_state_m h_final hs /\ is_valid_context2 h_final ctx2
  );
  res

#pop-options

#push-options "--z3refresh --z3rlimit 60 --max_fuel 4 --max_ifuel 4"
let responder_construct_msg2 kcs rs hs msg2
  = ST.push_frame ();
  (**) let h0 = ST.get () in

  // randomly generate connection ID C_R
  let c_R = create (size SpecParser.c_id_size) (u8 0) in
  crypto_random c_R (size SpecParser.c_id_size);
  // get credential cred_R
  let cred_R = create (size SpecParser.cred_size) (u8 0) in
  copy cred_R rs.id_cred;
  (**) let h1 = ST.get() in

  // construct context2
  let ctx2: context2 kcs = {
    c_r = c_R;
    id_cred_r = rs.id_cred;
    th2 = hs.th2.value;
    cred_r = cred_R;
  } in
  (**) let h2 = ST.get() in

  let res = responder_construct_msg2_uti #kcs hs ctx2 msg2.c2 in
  (**) let h3 = ST.get () in
  (**) assert(
    match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h2 h3
      | TypeEdhoc.CSuccess -> modifies1 msg2.c2 h2 h3
      | _ -> False
  );

  ST.pop_frame ();
  (**) let h_final = ST.get () in
  (**) assert(~(live h_final c_R) /\ ~(live h_final cred_R));
  (**) assume(
    match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h_final
      | TypeEdhoc.CSuccess -> modifies1 msg2.c2 h0 h_final
      | _ -> False
  );
  // (**) assert(is_valid_handshake_state_m h_final hs
  //     /\ is_valid_party_state_m h_final rs
  //     /\ is_valid_message2 h_final msg2
  // );
  res

#pop-options

#push-options "--z3refresh --z3rlimit 60 --max_fuel 4 --max_ifuel 4"
let responder_send_msg2_set_up_uti (kcs: supportedKemCipherSuite)
  (rs: party_state_m kcs) (hs: handshake_state_m kcs)
  (msg1: message1 kcs) (msg2: message2 kcs)
  : ST.Stack unit
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
    /\ is_valid_party_state_m h0 rs
    /\ is_valid_message1 h0 msg1 /\ is_legit_message1 h0 msg1
    /\ is_valid_message2 h0 msg2
    /\ live h0 kem_state /\ live h0 entropy_p

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs rs
    /\ handshake_state_m_disjoint_to_msg1 hs msg1
    /\ handshake_state_m_disjoint_to_msg2 hs msg2
    /\ handshake_state_m_disjoint_to_lbuffer hs kem_state
    /\ handshake_state_m_disjoint_to_lbuffer hs entropy_p
    /\ party_state_disjoint_to_msg1 rs msg1
    /\ party_state_disjoint_to_msg2 rs msg2
    /\ party_state_disjoint_to_lbuffer rs kem_state
    /\ party_state_disjoint_to_lbuffer rs entropy_p
    /\ message1_disjoint_to_lbuffer msg1 kem_state
    /\ message1_disjoint_to_lbuffer msg1 entropy_p
    /\ message2_disjoint_to_lbuffer msg2 kem_state
    /\ message2_disjoint_to_lbuffer msg2 entropy_p
    /\ message2_disjoint_to_msg1 msg2 msg1
    /\ disjoint kem_state entropy_p
  )
  (ensures fun h0 _ h1 ->
    let modified_locs = loc kem_state |+| loc entropy_p
              |+| lbufferOpt_loc hs.k_xy |+| loc msg2.ct_y
              |+| lbufferOpt_loc hs.k_auth_I |+| loc msg2.ct_auth_I
              |+| lbufferOpt_loc hs.th2 |+| lbufferOpt_loc hs.prk2e in

    modifies modified_locs h0 h1
    /\ lbufferOpt_is_Some h1 hs.k_xy /\ lbufferOpt_is_Some h1 hs.k_auth_I
    /\ lbufferOpt_is_Some h1 hs.th2 /\ lbufferOpt_is_Some h1 hs.prk2e
    /\ is_valid_handshake_state_m h1 hs
    /\ is_valid_party_state_m h1 rs
    /\ is_valid_message1 h0 msg1 /\ is_valid_message2 h0 msg2
  )
  = (**) let h0 = ST.get () in
  
  // ecnaps pk_x -> ct_y, k_xy
  kem_encaps kcs msg1.pk_x msg2.ct_y hs.k_xy.value;
  lbufferOpt_set_Some hs.k_xy; // set Some for k_xy
  (**) let h1 = ST.get () in
  (**) assert(modifies (loc kem_state |+| loc entropy_p
              |+| lbufferOpt_loc hs.k_xy |+| loc msg2.ct_y) h0 h1);

  // encaps pk_I -> ct_auth_I, k_auth_I
  let pk_I = rs.remote_static_kem_pub_key in
  kem_encaps kcs pk_I msg2.ct_auth_I hs.k_auth_I.value;
  lbufferOpt_set_Some hs.k_auth_I; // set Some for k_auth_I
  (**) let h2 = ST.get () in
  (**) assert(modifies (loc kem_state |+| loc entropy_p
              |+| lbufferOpt_loc hs.k_xy |+| loc msg2.ct_y
              |+| lbufferOpt_loc hs.k_auth_I |+| loc msg2.ct_auth_I) h0 h2);

  // derive TH2
  compute_th2 #kcs msg2.ct_y hs.k_auth_I.value msg1 hs.th2.value;
  lbufferOpt_set_Some hs.th2; // set Some for th2
  (**) let h3 = ST.get () in
  (**) assert(modifies (loc kem_state |+| loc entropy_p
              |+| lbufferOpt_loc hs.k_xy |+| loc msg2.ct_y
              |+| lbufferOpt_loc hs.k_auth_I |+| loc msg2.ct_auth_I
              |+| lbufferOpt_loc hs.th2) h0 h3);

  // derive PRK2e
  extract_prk2e #kcs hs.prk1e hs.th2.value hs.k_xy.value hs.prk2e.value;
  lbufferOpt_set_Some hs.prk2e; // set Some for prk2e
  ()


let responder_send_msg2_set_up kcs rs hs msg1 msg2
  = (**) let h0 = ST.get () in
  ST.push_frame ();

  responder_send_msg2_set_up_uti kcs rs hs msg1 msg2;

  // derive SAlT3e2m
  let salt3e2m = create (hash_size_t kcs) (u8 0) in
  expand_salt #kcs SpecKS.info_label_salt3e2m hs.prk2e.value hs.th2.value salt3e2m;

  // derive PRK3e2m
  extract_prk3e2m #kcs salt3e2m hs.k_auth_R hs.prk3e2m.value;
  lbufferOpt_set_Some hs.prk3e2m; // set Some for prk3e2m

  ST.pop_frame ();
  (**) let h_final = ST.get () in
  (**) assert(modifies (loc kem_state |+| loc entropy_p
              |+| lbufferOpt_loc hs.k_xy |+| loc msg2.ct_y
              |+| lbufferOpt_loc hs.k_auth_I |+| loc msg2.ct_auth_I
              |+| lbufferOpt_loc hs.th2
              |+| lbufferOpt_loc hs.prk2e |+| lbufferOpt_loc hs.prk3e2m) h0 h_final);
  ()

#pop-options
