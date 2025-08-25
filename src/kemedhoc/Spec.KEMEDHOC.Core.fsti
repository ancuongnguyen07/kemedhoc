module Spec.KEMEDHOC.Core

(*HACL libs*)
open Lib.IntTypes
// open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence
open Lib.RandomSequence

open FStar.Mul

open Spec.KEMEDHOC.Base.Definitions
open Spec.KEMEDHOC.CryptoPrimitives
open Spec.KEMEDHOC.Parser
open Spec.KEMEDHOC.KeySchedule
open Spec.KEMEDHOC.TranscriptHash
open Spec.KEMEDHOC.Ciphertext

module Seq = Lib.Sequence

(*---------------------------- Utilities*)
inline_for_extraction noextract
let kem_kp_equal (#kcs: supportedKemCipherSuite)
  (kp1 kp2: kemKeyPair kcs)
  = Seq.equal (get_pub_kem_key kp1) (get_pub_kem_key kp2)
  /\ Seq.equal (get_priv_kem_key kp1) (get_priv_kem_key kp2)

inline_for_extraction noextract
let option_lbyte_equal (#len: size_nat) (o1 o2: option (lbytes len))
  = (Some? o1 <==> Some? o2)
    /\ (Some? o1 ==> Seq.equal (Some?.v o1) (Some?.v o2))


(*---------------------------- Common between parties*)

/// -----------------
/// Party state
/// -----------------

noeq type party_state (#kcs: supportedKemCipherSuite) = {
  suite: supportedKemCipherSuiteLabel;
  static_kem_kp: kemKeyPair kcs;
  id_cred: id_cred_byte;
  // only Initiator needs the below ephemeral private key
  eph_kem_priv_key: option (kemPrivateKey kcs);
  remote_static_kem_pub_key: kemPublicKey kcs;
  remote_id_cred: id_cred_byte;
}

inline_for_extraction
type party_state_eph_est (#kcs: supportedKemCipherSuite) = p:party_state #kcs {
  Option.isSome p.eph_kem_priv_key
}

inline_for_extraction noextract
let ps_equal_non_eph (#kcs: supportedKemCipherSuite)
  (ps1 ps2: party_state #kcs)
  = ps1.suite = ps2.suite
    /\ kem_kp_equal ps1.static_kem_kp ps2.static_kem_kp
    /\ Seq.equal ps1.id_cred ps2.id_cred
    /\ Seq.equal ps1.remote_static_kem_pub_key ps2.remote_static_kem_pub_key
    /\ Seq.equal ps1.remote_id_cred ps2.remote_id_cred

inline_for_extraction noextract
let ps_equal_all (#kcs: supportedKemCipherSuite)
  (ps1 ps2: party_state #kcs)
  = ps_equal_non_eph ps1 ps2
    /\ option_lbyte_equal ps1.eph_kem_priv_key ps2.eph_kem_priv_key

val init_party_state:
  #kcs: supportedKemCipherSuite
  -> suite: supportedKemCipherSuiteLabel
  -> static_kem_kp: kemKeyPair kcs
  -> id_cred: id_cred_byte
  -> remote_static_kem_pub_key: kemPublicKey kcs
  -> remote_id_cred: id_cred_byte
  -> ps: party_state #kcs {~(Some? ps.eph_kem_priv_key)}

/// -----------------
/// Handshake state
/// -----------------

noeq type handshake_state (#kcs: supportedKemCipherSuite) = {
  suite_i: supportedKemCipherSuiteLabel;
  msg1_hash: hash_out kcs;
  k_xy: option (kemSharedSecret kcs);
  k_auth_R: kemSharedSecret kcs;
  k_auth_I: option (kemSharedSecret kcs);
  th1: hash_out kcs;
  th2: option (hash_out kcs);
  th3: option (hash_out kcs);
  th4: option (hash_out kcs);
  prk1e: hash_out kcs;
  prk2e: option (hash_out kcs);
  prk3e2m: option (hash_out kcs);
  prk4e3m: option (hash_out kcs);
  prk_out: option (hash_out kcs);
  prk_exporter: option (hash_out kcs);
  // ID credential of the remote party
  remote_id_cred: option id_cred_byte;
}

inline_for_extraction noextract
let hs_equal (#kcs: supportedKemCipherSuite)
  (hs1 hs2: handshake_state #kcs)
  = hs1.suite_i = hs2.suite_i
    /\ Seq.equal hs1.msg1_hash hs2.msg1_hash
    /\ option_lbyte_equal hs1.k_xy hs2.k_xy
    /\ option_lbyte_equal hs1.k_auth_I hs2.k_auth_I
    /\ Seq.equal hs1.k_auth_R hs2.k_auth_R
    /\ Seq.equal hs1.th1 hs2.th1
    /\ option_lbyte_equal hs1.th2 hs2.th2
    /\ option_lbyte_equal hs1.th3 hs2.th3
    /\ option_lbyte_equal hs1.th4 hs2.th4
    /\ Seq.equal hs1.prk1e hs2.prk1e
    /\ option_lbyte_equal hs1.prk2e hs2.prk2e
    /\ option_lbyte_equal hs1.prk3e2m hs2.prk3e2m
    /\ option_lbyte_equal hs1.prk4e3m hs2.prk4e3m
    /\ option_lbyte_equal hs1.prk_out hs2.prk_out
    /\ option_lbyte_equal hs1.prk_exporter hs2.prk_exporter

let hs_equal_after_msg1 (#kcs: supportedKemCipherSuite)
  (hs1 hs2: handshake_state #kcs)
  = hs1.suite_i = hs2.suite_i
    /\ Seq.equal hs1.msg1_hash hs2.msg1_hash
    /\ Seq.equal hs1.k_auth_R hs2.k_auth_R
    /\ Seq.equal hs1.th1 hs2.th1
    /\ Seq.equal hs1.prk1e hs2.prk1e

/// -------- Initial state
type handshake_state_init (#kcs: supportedKemCipherSuite)
  = hs:handshake_state #kcs {
    hs.suite_i = Some?.v (get_kemCipherSuite_label kcs)
    /\ Option.isNone hs.k_xy
    /\ Option.isNone hs.k_auth_I
    /\ Option.isNone hs.th2
    /\ Option.isNone hs.th3
    /\ Option.isNone hs.th4
    /\ Option.isNone hs.prk2e
    /\ Option.isNone hs.prk3e2m
    /\ Option.isNone hs.prk4e3m
    /\ Option.isNone hs.prk_out
    /\ Option.isNone hs.prk_exporter
  }

val init_handshake_state:
  #kcs: supportedKemCipherSuite
  -> msg1_hash: hash_out kcs
  -> th1: hash_out kcs
  -> k_auth_R: kemSharedSecret kcs
  -> prk1e: hash_out kcs
  -> handshake_state_init #kcs

/// -------- After Msg2

/// Valid transition of `handshake` during the handshake process.
type handshake_state_after_msg2 (#kcs: supportedKemCipherSuite)
  = hs:handshake_state #kcs {
    Option.isSome hs.k_auth_I
    /\ Option.isSome hs.k_xy
    /\ Option.isSome hs.th2
    /\ Option.isSome hs.prk2e
    /\ Option.isSome hs.prk3e2m

    /\ Option.isNone hs.prk4e3m
    /\ Option.isNone hs.prk_out
    /\ Option.isNone hs.prk_exporter
  }

let hs_equal_after_msg2 (#kcs: supportedKemCipherSuite)
  (hs1 hs2: handshake_state_after_msg2 #kcs)
  = Seq.equal (Some?.v hs1.k_xy) (Some?.v hs2.k_xy)
    /\ Seq.equal (Some?.v hs1.k_auth_I) (Some?.v hs2.k_auth_I)
    /\ Seq.equal (Some?.v hs1.th2) (Some?.v hs2.th2)
    /\ Seq.equal (Some?.v hs1.prk2e) (Some?.v hs2.prk2e)
    /\ Seq.equal (Some?.v hs1.prk3e2m) (Some?.v hs2.prk3e2m)
    

/// -------- After Msg3

type handshake_state_after_msg3 (#kcs: supportedKemCipherSuite)
  = hs:handshake_state #kcs {
    // fields should be Some after msg2
    Option.isSome hs.k_auth_I
    /\ Option.isSome hs.k_xy
    /\ Option.isSome hs.th2
    /\ Option.isSome hs.prk2e
    /\ Option.isSome hs.prk3e2m
    // fields should be Some after Msg3
    /\ Option.isSome hs.th3
    /\ Option.isSome hs.prk4e3m
    /\ Option.isSome hs.prk_out
    /\ Option.isSome hs.prk_exporter
  }

let hs_equal_after_msg3 (#kcs: supportedKemCipherSuite)
  (hs1 hs2: handshake_state_after_msg3 #kcs)
  = Seq.equal (Some?.v hs1.th3) (Some?.v hs2.th3)
    /\ Seq.equal (Some?.v hs1.prk4e3m) (Some?.v hs2.prk4e3m)
    /\ Seq.equal (Some?.v hs1.prk_out) (Some?.v hs2.prk_out)
    /\ Seq.equal (Some?.v hs1.prk_exporter) (Some?.v hs2.prk_exporter)

/// Valid transition of `handshake` during the handshake process.

let valid_hs_msg1_to_msg2 (#kcs: supportedKemCipherSuite)
  (hs1: handshake_state_init #kcs) (hs2: handshake_state_after_msg2 #kcs)
  = hs_equal_after_msg1 hs1 hs2

let valid_hs_msg2_to_msg3 (#kcs: supportedKemCipherSuite)
  (hs1: handshake_state_after_msg2 #kcs) (hs2: handshake_state_after_msg3 #kcs)
  = // unchange from msg1
  hs1.suite_i = hs2.suite_i
    /\ Seq.equal hs1.msg1_hash hs2.msg1_hash
    /\ Seq.equal hs1.k_auth_R hs2.k_auth_R
    /\ Seq.equal hs1.th1 hs2.th1
    /\ Seq.equal hs1.prk1e hs2.prk1e
  // unchanged from msg2
    /\ Seq.equal (Some?.v hs1.k_xy) (Some?.v hs2.k_xy)
    /\ Seq.equal (Some?.v hs1.k_auth_I) (Some?.v hs2.k_auth_I)
    /\ Seq.equal (Some?.v hs1.th2) (Some?.v hs2.th2)
    /\ Seq.equal (Some?.v hs1.prk2e) (Some?.v hs2.prk2e)
    /\ Seq.equal (Some?.v hs1.prk3e2m) (Some?.v hs2.prk3e2m)


/// Preconditions for two parties to start a KEMEDHOC handshake.
let precond_parties_setup (kcs: supportedKemCipherSuite)
  (is: party_state #kcs) (rs: party_state #kcs) (entr: entropy)
  = Seq.equal is.id_cred rs.remote_id_cred
  /\ Seq.equal rs.id_cred is.remote_id_cred
  /\ Seq.equal is.remote_static_kem_pub_key (get_pub_kem_key rs.static_kem_kp)
  /\ Seq.equal rs.remote_static_kem_pub_key (get_pub_kem_key is.static_kem_kp)
  /\ (
    /// the correctness of KEM authentication
    let pk_R, sk_R = rs.static_kem_kp in
    let pk_I, sk_I = is.static_kem_kp in

    let ct_R, k_R = kem_encaps kcs entr pk_R in
    let ct_I, k_I = kem_encaps kcs entr pk_I in

    let decaped_k_R = kem_decaps kcs ct_R sk_R in
    let decaped_k_I = kem_decaps kcs ct_I sk_I in

    Seq.equal k_R decaped_k_R
    /\ Seq.equal k_I decaped_k_I
  )

(*------------------ Message 1*)

/// Initiator sends message 1
val initiator_send_msg1:
  kcs: supportedKemCipherSuite
  -> is: party_state #kcs
  -> entr: entropy
  -> eresult (message1 #kcs & party_state_eph_est #kcs & handshake_state_init #kcs)

/// Responder processes message 1
val responder_process_msg1:
  kcs: supportedKemCipherSuite
  -> rs: party_state #kcs
  -> msg1: message1 #kcs
  -> eresult (handshake_state_init #kcs & plaintext1)

/// Bundle message1
noextract
val bundle_msg1:
  kcs: supportedKemCipherSuite
  -> is: party_state #kcs
  -> rs: party_state #kcs
  -> entr: entropy
  -> eresult (message1 #kcs & handshake_state_init #kcs
    & handshake_state_init #kcs & party_state_eph_est #kcs
    & party_state #kcs & plaintext1)

(*------------------ Message 2*)

/// Responder sends message 2
val responder_send_msg2:
  kcs: supportedKemCipherSuite
  -> rs: party_state #kcs
  -> hs: handshake_state_init #kcs
  -> msg1: message1 #kcs
  -> entr: entropy
  -> eresult (message2 #kcs & handshake_state_after_msg2 #kcs)

/// Initiator processes message 2
val initiator_process_msg2:
  kcs: supportedKemCipherSuite
  -> is: party_state_eph_est #kcs
  -> hs: handshake_state_init #kcs
  -> msg2: message2 #kcs
  -> eresult (handshake_state_after_msg2 #kcs & plaintext2 #kcs)

/// Bundle message1/2
noextract
val bundle_msg1_msg2:
  kcs: supportedKemCipherSuite
  -> is: party_state #kcs
  -> rs: party_state #kcs
  -> entr: entropy
  -> eresult (message2 #kcs & handshake_state_after_msg2 #kcs
    & handshake_state_after_msg2 #kcs & party_state_eph_est #kcs
    & party_state #kcs & plaintext2 #kcs)

(*------------------ Message 3*)

/// Initiator sends message 3
val initiator_send_msg3:
  kcs: supportedKemCipherSuite
  -> is: party_state_eph_est #kcs
  -> hs: handshake_state_after_msg2 #kcs
  -> ptx2: plaintext2 #kcs
  -> msg2: message2 #kcs
  -> eresult (message3 kcs & handshake_state_after_msg3 #kcs)

/// Responder processes message 3
val responder_process_msg3:
  kcs: supportedKemCipherSuite
  -> rs: party_state #kcs
  -> hs: handshake_state_after_msg2 #kcs
  -> ptx2: plaintext2 #kcs
  -> msg3: message3 kcs
  -> eresult (handshake_state_after_msg3 #kcs & plaintext3 #kcs)

/// Bundle message1/2/3
noextract
val bundle_msg1_msg2_msg3:
  kcs: supportedKemCipherSuite
  -> is: party_state #kcs
  -> rs: party_state #kcs
  -> entr: entropy
  -> eresult (message3 kcs & handshake_state_after_msg3 #kcs
    & handshake_state_after_msg3 #kcs & party_state_eph_est #kcs
    & party_state #kcs & plaintext3 #kcs)