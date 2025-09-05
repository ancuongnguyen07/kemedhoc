module Spec.EDHOC.Core

open FStar.Mul
open FStar.List.Tot

open Spec.EDHOC.Base.Definitions
open Spec.EDHOC.Serialization
open Spec.EDHOC.Parser
// friend Spec.EDHOC.Parser
open Spec.EDHOC.CryptoPrimitives
open Spec.EDHOC.Ciphertext
open Spec.EDHOC.CommonPred
open Spec.EDHOC.KeySchedule
open Spec.EDHOC.TranscriptHash

(*HACL libs*)
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

module Seq = Lib.Sequence
module HACLRandom = Lib.RandomSequence

(*---------------------------- Common between parties*)

/// Party's state, set up states for party without agreed-cipherSuite
noeq type party_state_initial = {
  suites:  supported_cipherSuite_label;
  method: method_enum;
}

/// Party's state, keep track of party-specific fields on agreed-cipherSuite
noeq type party_state (#cs:supported_cipherSuite) = {
  suites:  supported_cipherSuite_label;
  static_dh: ec_keypair cs;
  signature_key: ec_signature_keypair cs;
  id_cred: id_cred_i_bytes;
  eph_ec_keypair: option (ec_keypair cs);
  // The other party's public authentication key
  // this key should be pre-provisioned out-of-band
  remote_static_pub_key: (ec_pub_key cs);
  remote_signature_pub_key: (ec_signature_pub_key cs);
  remote_id_cred: id_cred_i_bytes;
}

// party state after a private/public EC share component
// x-G_x or y-G_y is randomly generated
type party_state_shared_est (#cs:supported_cipherSuite)
  = ps:party_state #cs {
    Option.isSome ps.eph_ec_keypair
  }

inline_for_extraction noextract
let ec_keypair_equal (#cs:supported_cipherSuite)
  (kp1 kp2:ec_keypair cs)
  : Type0
  = Seq.equal (kp1.pub) (kp2.pub)
  /\ Seq.equal (kp1.priv) (kp2.priv)

inline_for_extraction noextract
let ec_signature_keypair_equal (#cs:supported_cipherSuite)
  (kp1 kp2:ec_signature_keypair cs)
  : Type0
  = Seq.equal (kp1.pub) (kp2.pub)
  /\ Seq.equal (kp1.priv) (kp2.priv)

inline_for_extraction noextract
let ps_equal_non_shared_est (#cs:supported_cipherSuite)
  (ps1 ps2:party_state #cs)
  = ps1.suites = ps2.suites
  /\ ec_keypair_equal ps1.static_dh ps2.static_dh
  /\ ec_signature_keypair_equal ps1.signature_key ps2.signature_key
  /\ Seq.equal (ps1.id_cred) (ps2.id_cred)
  /\ Seq.equal (ps1.remote_static_pub_key) (ps2.remote_static_pub_key)
  /\ Seq.equal (ps1.remote_signature_pub_key) (ps2.remote_signature_pub_key)
  /\ Seq.equal (ps1.remote_id_cred) (ps2.remote_id_cred)


inline_for_extraction noextract
let ps_equal (#cs:supported_cipherSuite)
  (ps1 ps2:party_state #cs)
  = ps_equal_non_shared_est ps1 ps2
  /\ (Some? ps1.eph_ec_keypair <==> Some? ps2.eph_ec_keypair)
  /\ (Some? ps1.eph_ec_keypair ==> ec_keypair_equal (Some?.v ps1.eph_ec_keypair) (Some?.v ps2.eph_ec_keypair))

val init_party_state:
  #cs: supported_cipherSuite
  -> suites:  supported_cipherSuite_label
  -> static_dh: ec_keypair cs
  -> signature_key: ec_signature_keypair cs
  -> id_cred: id_cred_i_bytes
  // -> eph_ec_keypair: option (ec_keypair cs)
  -> remote_static_pub_key: (ec_pub_key cs)
  -> remote_signature_pub_key: (ec_signature_pub_key cs)
  -> remote_id_cred: id_cred_i_bytes
  -> Tot (party_state #cs)

(*Handshake state, used for tracking states of Initiator and Responder*)
noeq type handshake_state (#cs:supported_cipherSuite) = {
  // cipher suite chosen by Initiator
  suite_i: supported_cipherSuite_label;
  method: method_enum;
  // instead of storing `msg1` and `msg2`
  // just need to store `g_x` `g_y` and `hash_msg1`
  g_x: ec_pub_key cs;
  msg1_hash: hash_out cs;
  g_y: option (ec_pub_key cs);
  // msg1: option (message1 #cs);
  // authentication material used in msg2 is defined by Responder
  // msg2: option (message2 #cs #(get_auth_material Responder method));
  g_xy: option (shared_secret cs);
  g_rx: option (shared_secret cs);
  g_iy: option (shared_secret cs);
  th2: option (hash_out cs);
  th3: option (hash_out cs);
  th4: option (hash_out cs);
  prk2e: option (hash_out cs);
  prk3e2m: option (hash_out cs);
  prk4e3m: option (hash_out cs);
  prk_out: option (hash_out cs);
  prk_exporter: option (hash_out cs);
}

inline_for_extraction noextract
let hs_equal (#cs:supported_cipherSuite)
  (hs1 hs2:handshake_state #cs)
  :Type0
  = hs1.suite_i = hs2.suite_i /\ hs1.method == hs2.method
  /\ Seq.equal hs1.g_x hs2.g_x /\ Seq.equal hs1.msg1_hash hs2.msg1_hash
  /\ (Some? hs1.g_y <==> Some? hs2.g_y)
  /\ (Some? hs1.g_y ==> Seq.equal (Some?.v hs1.g_y) (Some?.v hs2.g_y))
  /\ (Some? hs1.g_xy <==> Some? hs2.g_xy)
  /\ (Some? hs1.g_xy ==> Seq.equal (Some?.v hs1.g_xy) (Some?.v hs2.g_xy))
  /\ (Some? hs1.g_rx <==> Some? hs2.g_rx)
  /\ (Some? hs1.g_rx ==> Seq.equal (Some?.v hs1.g_rx) (Some?.v hs2.g_rx))
  /\ (Some? hs1.g_iy <==> Some? hs2.g_iy)
  /\ (Some? hs1.g_iy ==> Seq.equal (Some?.v hs1.g_iy) (Some?.v hs2.g_iy))
  /\ (Some? hs1.th2 <==> Some? hs2.th2)
  /\ (Some? hs1.th2 ==> Seq.equal (Some?.v hs1.th2) (Some?.v hs2.th2))
  /\ (Some? hs1.th3 <==> Some? hs2.th3)
  /\ (Some? hs1.th3 ==> Seq.equal (Some?.v hs1.th3) (Some?.v hs2.th3))
  /\ (Some? hs1.th4 <==> Some? hs2.th4)
  /\ (Some? hs1.th4 ==> Seq.equal (Some?.v hs1.th4) (Some?.v hs2.th4))
  /\ (Some? hs1.prk2e <==> Some? hs2.prk2e)
  /\ (Some? hs1.prk2e ==> Seq.equal (Some?.v hs1.prk2e) (Some?.v hs2.prk2e))
  /\ (Some? hs1.prk3e2m <==> Some? hs2.prk3e2m)
  /\ (Some? hs1.prk3e2m ==> Seq.equal (Some?.v hs1.prk3e2m) (Some?.v hs2.prk3e2m))
  /\ (Some? hs1.prk4e3m <==> Some? hs2.prk4e3m)
  /\ (Some? hs1.prk4e3m ==> Seq.equal (Some?.v hs1.prk4e3m) (Some?.v hs2.prk4e3m))
  /\ (Some? hs1.prk_out <==> Some? hs2.prk_out)
  /\ (Some? hs1.prk_out ==> Seq.equal (Some?.v hs1.prk_out) (Some?.v hs2.prk_out))
  /\ (Some? hs1.prk_exporter <==> Some? hs2.prk_exporter)
  /\ (Some? hs1.prk_exporter ==> Seq.equal (Some?.v hs1.prk_exporter) (Some?.v hs2.prk_exporter)) 

type handshake_state_after_msg1 (#cs:supported_cipherSuite)
  // (#auth_material_r:authentication_material)
  = hs:handshake_state #cs {
    // Option.isSome hs.msg1
    True
  }

let hs_equal_after_msg1 (#cs:supported_cipherSuite)
  (hs1 hs2:handshake_state_after_msg1 #cs)
  = hs1.suite_i = hs2.suite_i /\ hs1.method == hs2.method
  /\ Seq.equal hs1.g_x hs2.g_x /\ Seq.equal hs1.msg1_hash hs2.msg1_hash

type handshake_state_after_msg2 (#cs:supported_cipherSuite)
  // (#auth_material_r:authentication_material)
  = hs:handshake_state_after_msg1 #cs {
    Option.isSome hs.th2
    /\ Option.isSome hs.g_y
    // /\ Option.isSome hs.msg2
    /\ Option.isSome hs.g_xy /\ Option.isSome hs.prk3e2m
    /\ Option.isSome hs.prk2e
  }

let hs_equal_after_msg2 (#cs:supported_cipherSuite)
  (hs1 hs2:handshake_state_after_msg1 #cs)
  = hs_equal_after_msg1 hs1 hs2
  /\ (Some? hs1.g_y <==> Some? hs2.g_y)
  /\ (Some? hs1.g_y ==> Seq.equal (Some?.v hs1.g_y) (Some?.v hs2.g_y))
  /\ (Some? hs1.g_xy <==> Some? hs2.g_xy)
  /\ (Some? hs1.g_xy ==> Seq.equal (Some?.v hs1.g_xy) (Some?.v hs2.g_xy))
  /\ (Some? hs1.th2 <==> Some? hs2.th2)
  /\ (Some? hs1.th2 ==> Seq.equal (Some?.v hs1.th2) (Some?.v hs2.th2))
  /\ (Some? hs1.prk2e <==> Some? hs2.prk2e)
  /\ (Some? hs1.prk2e ==> Seq.equal (Some?.v hs1.prk2e) (Some?.v hs2.prk2e))
  /\ (Some? hs1.prk3e2m <==> Some? hs2.prk3e2m)
  /\ (Some? hs1.prk3e2m ==> Seq.equal (Some?.v hs1.prk3e2m) (Some?.v hs2.prk3e2m))


type handshake_state_after_msg3 (#cs:supported_cipherSuite)
  // (#auth_material_r:authentication_material)
  = hs:handshake_state_after_msg2 #cs {
    Option.isSome hs.th3 /\ Option.isSome hs.th4
    /\ Option.isSome hs.prk4e3m /\ Option.isSome hs.prk_out
    /\ Option.isSome hs.prk_exporter
  }

let hs_equal_after_msg3 (#cs:supported_cipherSuite)
  (hs1 hs2:handshake_state_after_msg2 #cs)
  = hs_equal_after_msg1 hs1 hs2
  /\ hs_equal_after_msg2 hs1 hs2
  /\ (Some? hs1.th3 <==> Some? hs2.th3)
  /\ (Some? hs1.th3 ==> Seq.equal (Some?.v hs1.th3) (Some?.v hs2.th3))
  /\ (Some? hs1.th4 <==> Some? hs2.th4)
  /\ (Some? hs1.th4 ==> Seq.equal (Some?.v hs1.th4) (Some?.v hs2.th4))
  /\ (Some? hs1.prk4e3m <==> Some? hs2.prk4e3m)
  /\ (Some? hs1.prk4e3m ==> Seq.equal (Some?.v hs1.prk4e3m) (Some?.v hs2.prk4e3m))
  /\ (Some? hs1.prk_out <==> Some? hs2.prk_out)
  /\ (Some? hs1.prk_out ==> Seq.equal (Some?.v hs1.prk_out) (Some?.v hs2.prk_out))
  /\ (Some? hs1.prk_exporter <==> Some? hs2.prk_exporter)
  /\ (Some? hs1.prk_exporter ==> Seq.equal (Some?.v hs1.prk_exporter) (Some?.v hs2.prk_exporter))

/// This handshake_state initialization shoudl be run
/// before Initiator constructs the message 1
val init_handshake_state:
  cs:supported_cipherSuite
  -> method: method_enum
  -> g_x: ec_pub_key cs
  -> msg1_hash: hash_out cs
  -> Tot (handshake_state #cs)


val party_set_up:
  cipherSuite_:  supported_cipherSuite_label
  -> method: method_enum
  -> Tot party_state_initial


(*---------------------------- Common derivation*)
/// Intermediate-private function: derive PRK3e2m
val derive_prk3e2m:
  #cs:supported_cipherSuite
  -> auth_material:authentication_material
  -> prk2e:hash_out cs
  -> th2:hash_out cs
  -> r:option (ec_priv_key cs)
  {(auth_material == MAC) ==> Some? r}
  -> pub_r:option (ec_pub_key cs){
    (auth_material == MAC) ==> Some? pub_r
  }
  -> eresult (hash_out cs)

/// Intermediate-private function: derive PRK4e3m
val derive_prk4e3m:
  #cs:supported_cipherSuite
  -> auth_material:authentication_material
  -> prk3e2m:hash_out cs
  -> th3:hash_out cs
  -> i:option (ec_priv_key cs)
  {(auth_material == MAC) ==> Some? i}
  -> pub_i:option (ec_pub_key cs){
    (auth_material == MAC) ==> Some? pub_i
  }
  -> eresult (hash_out cs)


(*---------------------------- Initiator side*)

/// Verify Sig_or_MAC2
val verify_sig_or_mac2:
  #cs:supported_cipherSuite
  -> auth_material:authentication_material
  -> sig_or_mac2:lbytes (sig_or_mac23_size cs auth_material)
  -> mac2:lbytes (mac23_size cs auth_material)
  -> c2:context2 #cs
  -> pk_r:option (ec_signature_pub_key cs){
    auth_material == Signature ==> Some? pk_r
  }
  -> bool

/// Derive Sig_or_MAC3
val derive_sig_or_mac3:
  #cs:supported_cipherSuite
  -> auth_material:authentication_material
  -> entr: HACLRandom.entropy
  -> sk_i_op:option (ec_signature_priv_key cs){
    auth_material == Signature ==> Some? sk_i_op
  }
  -> mac3:lbytes (mac23_size cs auth_material)
  -> c3:context3 #cs
  -> option (sig_or_mac23_bytes cs auth_material)


/// Initiator initially choose a cipher suite
/// then send along with message 1

val initiator_send_msg1:
  cs:supported_cipherSuite
  -> method: method_enum
  -> entr: HACLRandom.entropy
  -> is: party_state #cs // initiator's state
  -> Tot (eresult (message1 #cs & party_state_shared_est #cs & handshake_state_after_msg1 #cs))

/// This process msg2 and send msg3
val initiator_process_msg2:
  #cs:supported_cipherSuite
  -> is:party_state_shared_est #cs // initiator's state
  -> hs:handshake_state_after_msg1 #cs // initiator's handshake state
  -> msg2:message2 #cs #(get_auth_material Responder hs.method)
  -> Tot (eresult (plaintext2 #cs #(get_auth_material Responder hs.method)
                    & handshake_state_after_msg2 #cs))

val initiator_send_msg3:
  #cs:supported_cipherSuite
  -> entr:HACLRandom.entropy
  -> is:party_state_shared_est #cs // initiator's state
  -> hs:handshake_state_after_msg2 #cs // initiator's handshake state
  -> plaintext2 #cs #(get_auth_material Responder hs.method)
  -> Tot (eresult (message3 #cs & handshake_state_after_msg3 #cs))

// let lemma_initiator_send_msg3_decrypt_equiv
//   (#cs:)

(*---------------------------- Responder side*)
/// Responder returns whether it supports the cipher suite
/// chosen from Initiator. Currently not used, integrated
/// into `responder_process_msg1`
// val responder_agree_cipherSuite:
//   intitator_state: party_state_initial
//   -> Tot (eresult party_state_initial)

/// Verify Sig_or_MAC3
val verify_sig_or_mac3:
  #cs:supported_cipherSuite
  -> auth_material:authentication_material
  -> sig_or_mac3:lbytes (sig_or_mac23_size cs auth_material)
  -> mac3:lbytes (mac23_size cs auth_material)
  -> c3:context3 #cs
  -> pk_i_op:option (ec_signature_pub_key cs){
    auth_material == Signature ==> Some? pk_i_op
  }
  -> bool

/// This process msg1 and send msg2
val responder_process_msg1:
  #cs:supported_cipherSuite
  -> rs:party_state #cs // responder's state
  // -> hs:handshake_state #cs
  -> msg1:message1 #cs
  -> Tot (eresult (handshake_state_after_msg1 #cs))

/// Intermediate-private function: derive Signature2
val derive_sig_or_mac2:
  #cs:supported_cipherSuite
  -> auth_material:authentication_material
  -> entr: HACLRandom.entropy
  -> sk_r_op:option (ec_signature_priv_key cs){
    auth_material == Signature ==> Some? sk_r_op
  }
  -> mac2:lbytes (mac23_size cs auth_material)
  -> c2:context2 #cs
  -> option (sig_or_mac23_bytes cs auth_material)

val responder_send_msg2:
  #cs:supported_cipherSuite
  -> entr: HACLRandom.entropy
  -> rs:party_state #cs
  -> hs:handshake_state_after_msg1 #cs
  -> Tot (eresult (plaintext2 #cs #(get_auth_material Responder hs.method)
                  & message2 #cs #(get_auth_material Responder hs.method)
                  & party_state_shared_est #cs & handshake_state_after_msg2 #cs))

// Return prk_exporter as the shared session key
val responder_process_msg3:
  #cs:supported_cipherSuite
  -> rs:party_state_shared_est #cs
  -> hs:handshake_state_after_msg2 #cs
  -> plaintext2 #cs #(get_auth_material Responder hs.method)
  -> msg3:message3 #cs
  -> Tot (eresult (handshake_state_after_msg3 #cs))

(*------------------------------------*)
(*----------------------------- LEMMAS*)
(*------------------------------------*)

(*---------------- Handshake state transition *)
inline_for_extraction noextract
let valid_hs_msg1_to_msg2
  (#cs:supported_cipherSuite) (hs':handshake_state_after_msg1 #cs)
  (hs'':handshake_state_after_msg2 #cs)
  = hs'.method = hs''.method
  /\ hs'.suite_i = hs''.suite_i
  /\ lbytes_eq hs'.g_x hs''.g_x
  /\ lbytes_eq hs'.msg1_hash hs''.msg1_hash


inline_for_extraction noextract
let valid_hs_msg2_to_msg3
  (#cs:supported_cipherSuite) (hs'':handshake_state_after_msg2 #cs)
  (hs''':handshake_state_after_msg3 #cs)
  = valid_hs_msg1_to_msg2 hs'' hs'''
  /\ lbytes_eq (Some?.v hs''.th2) (Some?.v hs'''.th2)
  /\ lbytes_eq (Some?.v hs''.g_xy) (Some?.v hs'''.g_xy)
  /\ lbytes_eq (Some?.v hs''.prk2e) (Some?.v hs'''.prk2e)
  /\ lbytes_eq (Some?.v hs''.prk3e2m) (Some?.v hs'''.prk3e2m)
  /\ lbytes_eq (Some?.v hs''.g_y) (Some?.v hs'''.g_y)
  // /\ (Some?.v hs''.msg2) == (Some?.v hs'''.msg2)
  // /\ eqb_from_prop (Some?.v hs''.msg2) (Some?.v hs'''.msg2)

/// --------------------------
/// Post-conditions for `handshake_state` after each message
/// and for `party_state` after an ephemeral share is established
/// --------------------------

inline_for_extraction noextract
let post_hs_after_msg1 (#cs:supported_cipherSuite)
  (hs_i':handshake_state_after_msg1 #cs) (hs_r':handshake_state_after_msg1 #cs)
  : Type0
  = hs_r'.method = hs_i'.method
  /\ hs_r'.suite_i = hs_i'.suite_i
  /\ lbytes_eq hs_i'.g_x hs_r'.g_x
  /\ lbytes_eq hs_i'.msg1_hash hs_r'.msg1_hash

inline_for_extraction noextract
let post_hs_after_msg2 (#cs:supported_cipherSuite)
  (hs_i'':handshake_state_after_msg2 #cs) (hs_r'':handshake_state_after_msg2 #cs)
  = post_hs_after_msg1 hs_i'' hs_r''
  /\ lbytes_eq (Some?.v hs_i''.th2) (Some?.v hs_r''.th2)
  /\ lbytes_eq (Some?.v hs_i''.g_xy) (Some?.v hs_r''.g_xy)
  /\ lbytes_eq (Some?.v hs_i''.prk2e) (Some?.v hs_r''.prk2e)
  /\ lbytes_eq (Some?.v hs_i''.prk3e2m) (Some?.v hs_r''.prk3e2m)
  /\ lbytes_eq (Some?.v hs_i''.g_y) (Some?.v hs_r''.g_y)

inline_for_extraction noextract
let post_hs_after_msg3 (#cs:supported_cipherSuite)
  (hs_i''':handshake_state_after_msg3 #cs) (hs_r''':handshake_state_after_msg3 #cs)
  = post_hs_after_msg2 hs_i''' hs_r'''
    /\ lbytes_eq (Some?.v hs_i'''.th3) (Some?.v hs_r'''.th3)
    /\ lbytes_eq (Some?.v hs_i'''.th4) (Some?.v hs_r'''.th4)
    /\ lbytes_eq (Some?.v hs_i'''.prk4e3m) (Some?.v hs_r'''.prk4e3m)
    /\ lbytes_eq (Some?.v hs_i'''.prk_out) (Some?.v hs_r'''.prk_out)
    /\ lbytes_eq (Some?.v hs_i'''.prk_exporter) (Some?.v hs_r'''.prk_exporter)

(* party_state = {
  suites:  supported_cipherSuite_label;
  static_dh: ec_keypair cs;
  signature_key: ec_signature_keypair cs;
  id_cred: id_cred_i_bytes;
  eph_ec_keypair: option (ec_keypair cs);
  // The other party's public authentication key
  // this key should be pre-provisioned out-of-band
  remote_static_pub_key: (ec_pub_key cs);
  remote_signature_pub_key: (ec_signature_pub_key cs);
  remote_id_cred: id_cred_i_bytes;
}
*)
let equal_ec_keypair (#cs:supported_cipherSuite)
  (kp:ec_keypair cs) (kp':ec_keypair cs)
  = lbytes_eq kp.pub kp'.pub
  /\ lbytes_eq kp.priv kp'.priv

let equal_ecdsa_keypair (#cs:supported_cipherSuite)
  (kp:ec_signature_keypair cs) (kp':ec_signature_keypair cs)
  = lbytes_eq kp.pub kp'.pub
  /\ lbytes_eq kp.priv kp'.priv

inline_for_extraction noextract
let post_ps_unchanged_fixed_vals (#cs:supported_cipherSuite)
  (ps:party_state #cs) (ps':party_state #cs)
  = ps.suites = ps'.suites
  /\ equal_ec_keypair ps.static_dh ps'.static_dh
  /\ equal_ecdsa_keypair ps.signature_key ps'.signature_key
  /\ lbytes_eq ps.id_cred ps'.id_cred
  /\ lbytes_eq ps.remote_static_pub_key ps'.remote_static_pub_key
  /\ lbytes_eq ps.remote_signature_pub_key ps'.remote_signature_pub_key
  /\ lbytes_eq ps.remote_id_cred ps'.remote_id_cred

inline_for_extraction noextract
let post_ps_unchanged_all_vals (#cs:supported_cipherSuite)
  (ps:party_state #cs) (ps':party_state #cs)
  = post_ps_unchanged_fixed_vals #cs ps ps'
  /\ Some? ps.eph_ec_keypair <==> Some? ps'.eph_ec_keypair
  /\ (Some? ps.eph_ec_keypair ==> (
    let kp = Some?.v ps.eph_ec_keypair in
    let kp' = Some?.v ps'.eph_ec_keypair in

    equal_ec_keypair kp kp'
  ))

  