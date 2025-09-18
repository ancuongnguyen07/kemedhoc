module Impl.KEMEDHOC.Core

(*LowStar related modules*)
open Lib.ByteBuffer
open Lib.IntTypes
open Lib.Buffer

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module Spec = Spec.KEMEDHOC.Core
module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives

(*EDHOC utilities*)
// open Impl.EDHOC.Utilities

(*KEMEDHOC utilities*)
open Impl.KEMEDHOC.Types
open Impl.KEMEDHOC.CryptoPrimitives
// open Impl.KEMEDHOC.KeySchedule
open Impl.KEMEDHOC.Parser
// open Impl.KEMEDHOC.Ciphertext
// open Impl.KEMEDHOC.TranscriptHash
open Spec.KEMEDHOC.Base.Definitions

(*Specification modules*)
module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecSerdEdhoc = Spec.EDHOC.Serialization
module SpecParser = Spec.KEMEDHOC.Parser

module TypeEdhoc = TypeHelper.EDHOC

(*--------------------------- Utilities*)
let kem_key_pair_m_live (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (kp: kem_key_pair_m kcs)
  = match kp with
    | pub_key, priv_key -> live h pub_key /\ live h priv_key

let kem_key_pair_m_disjoint (#kcs: supportedKemCipherSuite)
  (kp: kem_key_pair_m kcs)
  = match kp with
    | pub_key, priv_key -> disjoint pub_key priv_key

let kem_key_pair_m_union (#kcs: supportedKemCipherSuite)
  (kp: kem_key_pair_m kcs)
  = match kp with
    | pub_key, priv_key -> loc pub_key |+| loc priv_key

let is_valid_kem_key_pair_m (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (kp: kem_key_pair_m kcs)
  = kem_key_pair_m_live h kp /\ kem_key_pair_m_disjoint kp

(*---------------------------- Common between parties*)

/// -----------------
/// Party state
/// -----------------
noeq type party_state_m (kcs: supportedKemCipherSuite) = {
  suite: lbuffer uint8 1ul;
  static_kem_kp: kem_key_pair_m kcs;
  id_cred: id_cred_buffer;
  // only Initiator needs the below ephemeral private key
  eph_kem_priv_key: lbufferOpt (kem_priv_key_size_t kcs);
  remote_static_kem_pub_key: kem_pub_key_buff kcs;
  remote_id_cred: cred_buffer;
}

let party_state_live (#kcs: supportedKemCipherSuite) (h: HS.mem)
  (ps: party_state_m kcs)
  = live h ps.suite /\ kem_key_pair_m_live h ps.static_kem_kp
    /\ live h ps.id_cred /\ lbufferOpt_live h ps.eph_kem_priv_key
    /\ live h ps.remote_static_kem_pub_key /\ live h ps.remote_id_cred

let party_state_disjoint (#kcs: supportedKemCipherSuite) (ps: party_state_m kcs)
  = B.all_disjoint [loc ps.suite; kem_key_pair_m_union ps.static_kem_kp;
      loc ps.id_cred; lbufferOpt_loc ps.eph_kem_priv_key;
      loc ps.remote_static_kem_pub_key; loc ps.remote_id_cred]
    /\ kem_key_pair_m_disjoint ps.static_kem_kp

let party_state_union (#kcs: supportedKemCipherSuite)
  (ps: party_state_m kcs)
  = loc ps.suite |+| kem_key_pair_m_union ps.static_kem_kp
    |+| loc ps.id_cred |+| lbufferOpt_loc ps.eph_kem_priv_key
    |+| loc ps.remote_static_kem_pub_key |+| loc ps.remote_id_cred

let party_state_disjoint_to_lbuffer (#t:buftype) (#a:Type0) (#kcs: supportedKemCipherSuite)
  (ps: party_state_m kcs) (buf: buffer_t t a)
  = disjoint buf ps.suite /\ disjoint buf ps.id_cred
    /\ lbufferOpt_disjoint_to_lbuff ps.eph_kem_priv_key buf /\ disjoint buf ps.remote_static_kem_pub_key
    /\ disjoint buf ps.remote_id_cred
    /\ disjoint buf (fst ps.static_kem_kp) /\ disjoint buf (snd ps.static_kem_kp)

let party_state_disjoint_to_msg1 (#kcs: supportedKemCipherSuite)
  (ps: party_state_m kcs) (m1: message1 kcs)
  = B.all_disjoint [loc ps.suite; loc (fst ps.static_kem_kp);
      loc (snd ps.static_kem_kp);
      loc ps.id_cred;
      loc ps.eph_kem_priv_key.is_some; loc ps.eph_kem_priv_key.value;
      loc ps.remote_static_kem_pub_key; loc ps.remote_id_cred;

      loc m1.method; loc m1.suite_i; loc m1.pk_x;
      loc m1.ct_auth_R; loc m1.c_i; loc m1.c1
    ]

let is_valid_party_state_m (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (ps: party_state_m kcs)
  = let suite_label = SpecSerdEdhoc.bytes_to_nat (as_seq h ps.suite) in
  
  party_state_live h ps /\ party_state_disjoint ps
  /\ suite_label = 9

type valid_party_state_m (kcs: supportedKemCipherSuite) (h: HS.mem)
  = ps:party_state_m kcs {is_valid_party_state_m h ps}

let is_party_state_eph_est_m (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (ps: party_state_m kcs)
  = is_valid_party_state_m h ps
    /\ lbufferOpt_is_Some h ps.eph_kem_priv_key

let party_state_m_eval (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (ps: valid_party_state_m kcs h)
  : GTot (Spec.party_state #kcs)
  = let suite_label = SpecSerdEdhoc.bytes_to_nat (as_seq h ps.suite) in 
  {
    Spec.suite = suite_label;
    Spec.static_kem_kp = kem_key_pair_m_eval h ps.static_kem_kp;
    Spec.id_cred = as_seq h ps.id_cred;
    Spec.eph_kem_priv_key = eval_lbuffer_opt h ps.eph_kem_priv_key;
    Spec.remote_static_kem_pub_key = as_seq h ps.remote_static_kem_pub_key;
    Spec.remote_id_cred = as_seq h ps.remote_id_cred;
  }

let lemma_ps_m_eval_equiv (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (ps: party_state_m kcs)
  : Lemma 
  (requires is_valid_party_state_m h ps)
  (ensures (
    let ps_s = party_state_m_eval #kcs h ps in

    Some? ps_s.eph_kem_priv_key <==> lbufferOpt_is_Some h ps.eph_kem_priv_key
  ))
  [SMTPat (party_state_m_eval #kcs h ps)]
  = ()

/// -----------------
/// Handshake state
/// -----------------
noeq type handshake_state_m (kcs: supportedKemCipherSuite) = {
  suite_i: lbuffer uint8 1ul;
  msg1_hash: hash_out_buff kcs;
  k_xy: lbufferOpt (kem_shared_secret_size_t kcs);
  k_auth_R: kem_shared_secret_buff kcs;
  k_auth_I: lbufferOpt (kem_shared_secret_size_t kcs);
  th1: hash_out_buff kcs;
  th2: lbufferOpt (hash_size_t kcs);
  th3: lbufferOpt (hash_size_t kcs);
  th4: lbufferOpt (hash_size_t kcs);
  prk1e: hash_out_buff kcs;
  prk2e: lbufferOpt (hash_size_t kcs);
  prk3e2m: lbufferOpt (hash_size_t kcs);
  prk4e3m: lbufferOpt (hash_size_t kcs);
  prk_out: lbufferOpt (hash_size_t kcs);
  prk_exporter: lbufferOpt (hash_size_t kcs);
  // ID credential of the remote party
  remote_id_cred: lbufferOpt (size SpecParser.cred_size);
}

let handshake_state_m_live (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (hs: handshake_state_m kcs)
  = live h hs.suite_i /\ live h hs.msg1_hash
    /\ lbufferOpt_live h hs.k_xy /\ live h hs.k_auth_R
    /\ lbufferOpt_live h hs.k_auth_I /\ live h hs.th1
    /\ lbufferOpt_live h hs.th2 /\ lbufferOpt_live h hs.th3
    /\ lbufferOpt_live h hs.th4 /\ live h hs.prk1e
    /\ lbufferOpt_live h hs.prk2e /\ lbufferOpt_live h hs.prk3e2m
    /\ lbufferOpt_live h hs.prk4e3m /\ lbufferOpt_live h hs.prk_out
    /\ lbufferOpt_live h hs.prk_exporter
    /\ lbufferOpt_live h hs.remote_id_cred

let handshake_state_m_disjoint (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (hs: handshake_state_m kcs)
  = B.all_disjoint [loc hs.suite_i; loc hs.msg1_hash;
      loc hs.k_xy.is_some; loc hs.k_xy.value;
      loc hs.k_auth_R;
      loc hs.k_auth_I.is_some; loc hs.k_auth_I.value;
      loc hs.th1;
      loc hs.th2.is_some; loc hs.th2.value;
      loc hs.th3.is_some; loc hs.th3.value;
      loc hs.th4.is_some; loc hs.th4.value;
      loc hs.prk1e; loc hs.prk2e.is_some; loc hs.prk2e.value;
      loc hs.prk3e2m.is_some; loc hs.prk3e2m.value;
      loc hs.prk4e3m.is_some; loc hs.prk4e3m.value;
      loc hs.prk_out.is_some; loc hs.prk_out.value;
      loc hs.prk_exporter.is_some; loc hs.prk_exporter.value;
      loc hs.remote_id_cred.is_some; loc hs.remote_id_cred.value]

let is_valid_handshake_state_m (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (hs: handshake_state_m kcs)
  = let suite_label = SpecSerdEdhoc.bytes_to_nat (as_seq h hs.suite_i) in
  handshake_state_m_live h hs /\ handshake_state_m_disjoint h hs
  /\ suite_label = 9

inline_for_extraction
type valid_handshake_state_m (kcs: supportedKemCipherSuite) (h: HS.mem)
  = hs:handshake_state_m kcs {is_valid_handshake_state_m h hs}

let handshake_state_m_union (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs)
  = loc hs.suite_i |+| loc hs.msg1_hash
    |+| lbufferOpt_loc hs.k_xy |+| loc hs.k_auth_R
    |+| lbufferOpt_loc hs.k_auth_I |+| loc hs.th1
    |+| lbufferOpt_loc hs.th2 |+| lbufferOpt_loc hs.th3
    |+| lbufferOpt_loc hs.th4 |+| loc hs.prk1e
    |+| lbufferOpt_loc hs.prk2e |+| lbufferOpt_loc hs.prk3e2m
    |+| lbufferOpt_loc hs.prk4e3m |+| lbufferOpt_loc hs.prk_out
    |+| lbufferOpt_loc hs.prk_exporter
    |+| lbufferOpt_loc hs.remote_id_cred

let handshake_state_m_disjoint_to_lbuffer (#t:buftype) (#a:Type0) (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (buf: buffer_t t a)
  = disjoint buf hs.suite_i /\ disjoint buf hs.msg1_hash
    /\ lbufferOpt_disjoint_to_lbuff hs.k_xy buf
    /\ disjoint buf hs.k_auth_R
    /\ lbufferOpt_disjoint_to_lbuff hs.k_auth_I buf /\ disjoint buf hs.th1
    /\ lbufferOpt_disjoint_to_lbuff hs.th2 buf
    /\ lbufferOpt_disjoint_to_lbuff hs.th3 buf
    /\ lbufferOpt_disjoint_to_lbuff hs.th4 buf /\ disjoint buf hs.prk1e
    /\ lbufferOpt_disjoint_to_lbuff hs.prk2e buf
    /\ lbufferOpt_disjoint_to_lbuff hs.prk3e2m buf
    /\ lbufferOpt_disjoint_to_lbuff hs.prk4e3m buf
    /\ lbufferOpt_disjoint_to_lbuff hs.prk_out buf
    /\ lbufferOpt_disjoint_to_lbuff hs.prk_exporter buf
    /\ lbufferOpt_disjoint_to_lbuff hs.remote_id_cred buf

let handshake_state_m_disjoint_to_party_state (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (ps: party_state_m kcs)
  = B.all_disjoint [loc hs.suite_i; loc hs.msg1_hash;
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

      loc ps.suite; kem_key_pair_m_union ps.static_kem_kp;
      loc ps.id_cred;
      loc ps.eph_kem_priv_key.is_some; loc ps.eph_kem_priv_key.value;
      loc ps.remote_static_kem_pub_key; loc ps.remote_id_cred
    ]

let handshake_state_m_disjoint_to_msg1 (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs) (m1: message1 kcs)
  = B.all_disjoint [loc hs.suite_i; loc hs.msg1_hash;
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
      loc hs.prk_out.is_some; loc hs.prk4e3m.value;
      loc hs.prk_exporter.is_some; loc hs.prk_exporter.value;
      loc hs.remote_id_cred.is_some; loc hs.remote_id_cred.value;

      loc m1.method; loc m1.suite_i; loc m1.pk_x;
      loc m1.ct_auth_R; loc m1.c_i; loc m1.c1
    ]

let handshake_state_m_eval (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (hs: valid_handshake_state_m kcs h)
  : GTot (Spec.handshake_state #kcs)
  = let suite_label = SpecSerdEdhoc.bytes_to_nat (as_seq h hs.suite_i) in
  {
    Spec.suite_i = suite_label;
    Spec.msg1_hash = as_seq h hs.msg1_hash;
    Spec.k_xy = eval_lbuffer_opt h hs.k_xy;
    Spec.k_auth_R = as_seq h hs.k_auth_R;
    Spec.k_auth_I = eval_lbuffer_opt h hs.k_auth_I;
    Spec.th1 = as_seq h hs.th1;
    Spec.th2 = eval_lbuffer_opt h hs.th2;
    Spec.th3 = eval_lbuffer_opt h hs.th3;
    Spec.th4 = eval_lbuffer_opt h hs.th4;
    Spec.prk1e = as_seq h hs.prk1e;
    Spec.prk2e = eval_lbuffer_opt h hs.prk2e;
    Spec.prk3e2m = eval_lbuffer_opt h hs.prk3e2m;
    Spec.prk4e3m = eval_lbuffer_opt h hs.prk4e3m;
    Spec.prk_out = eval_lbuffer_opt h hs.prk_out;
    Spec.prk_exporter = eval_lbuffer_opt h hs.prk_exporter;
    Spec.remote_id_cred = eval_lbuffer_opt h hs.remote_id_cred;
  }

/// Refined types for handshake state during the protocol run

let is_handshake_state_m_after_init (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (hs: handshake_state_m kcs)
  = is_valid_handshake_state_m h hs
  /\ lbufferOpt_is_None h hs.k_xy
    /\ lbufferOpt_is_None h hs.k_auth_I
    /\ lbufferOpt_is_None h hs.th2
    /\ lbufferOpt_is_None h hs.th3
    /\ lbufferOpt_is_None h hs.th4
    /\ lbufferOpt_is_None h hs.prk2e
    /\ lbufferOpt_is_None h hs.prk3e2m
    /\ lbufferOpt_is_None h hs.prk4e3m
    /\ lbufferOpt_is_None h hs.prk_out
    /\ lbufferOpt_is_None h hs.prk_exporter
    /\ lbufferOpt_is_None h hs.remote_id_cred

let is_valid_handshake_state_m_after_msg2 (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (hs: handshake_state_m kcs)
  = is_valid_handshake_state_m h hs
  // should be Some after Msg2
  /\ lbufferOpt_is_Some h hs.k_auth_I
  /\ lbufferOpt_is_Some h hs.k_xy
  /\ lbufferOpt_is_Some h hs.th2
  /\ lbufferOpt_is_Some h hs.prk2e
  /\ lbufferOpt_is_Some h hs.prk3e2m
  // should be None
  /\ lbufferOpt_is_None h hs.prk4e3m
  /\ lbufferOpt_is_None h hs.prk_out
  /\ lbufferOpt_is_None h hs.prk_exporter

let is_valid_handshake_state_m_after_msg3 (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (hs: handshake_state_m kcs)
  = is_valid_handshake_state_m h hs
  // should be Some
  /\ lbufferOpt_is_Some h hs.k_auth_I
  /\ lbufferOpt_is_Some h hs.k_xy
  /\ lbufferOpt_is_Some h hs.th2
  /\ lbufferOpt_is_Some h hs.prk2e
  /\ lbufferOpt_is_Some h hs.prk3e2m
  // should be Some after Msg3
  /\ lbufferOpt_is_Some h hs.prk4e3m
  /\ lbufferOpt_is_Some h hs.prk_out
  /\ lbufferOpt_is_Some h hs.prk_exporter

let modified_loc_hs_after_init (#kcs: supportedKemCipherSuite)
  (hs: handshake_state_m kcs)
  = loc hs.k_xy.is_some |+| loc hs.k_auth_I.is_some
    |+| loc hs.th2.is_some |+| loc hs.th3.is_some |+| loc hs.th4.is_some
    |+| loc hs.prk2e.is_some |+| loc hs.prk3e2m.is_some |+| loc hs.prk4e3m.is_some
    |+| loc hs.prk_out.is_some |+| loc hs.prk_exporter.is_some
    |+| loc hs.remote_id_cred.is_some

val init_handshake_state:
  #kcs: supportedKemCipherSuite
  -> hs: handshake_state_m kcs
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_handshake_state_m h0 hs
  )
  (ensures fun h0 _ h1 ->
    let hs_s = Spec.init_handshake_state #kcs (as_seq h0 hs.msg1_hash)
                (as_seq h0 hs.th1) (as_seq h0 hs.k_auth_R) (as_seq h0 hs.prk1e) in

    modifies (modified_loc_hs_after_init hs) h0 h1
    /\ is_handshake_state_m_after_init h1 hs
    /\ Spec.hs_equal (handshake_state_m_eval h1 hs) hs_s
  )
