module Impl.EDHOC.Core.Types

(*HACL related modules*)
open Lib.RawIntTypes
open Lib.IntTypes
// open Lib.Sequence
open Lib.ByteBuffer
// lbuffer type, an immutable buffer with
// length tag, is from this module
// let lbuffer (a:Type0) (len:size_t) = lbuffer_t MUT a len
// `live` and `disjoint` are also from this module.
// Basically, HACL `Lib.Buffer` is a wrapper of `LowStar.Buffer`
// and related LowStar memory models.
open Lib.Buffer

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

module Spec = Spec.EDHOC.Core
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecSerd = Spec.EDHOC.Serialization
module SpecParser = Spec.EDHOC.Parser

open Spec.EDHOC.Base.Definitions

open Impl.EDHOC.CryptoPrimitives
open Impl.EDHOC.KeySchedule
open Impl.EDHOC.Ciphertext
open Impl.EDHOC.TranscriptHash
open Impl.EDHOC.Parser
open Impl.EDHOC.Utilities
open TypeHelper.EDHOC

(*---------------------------- Common between parties*)
inline_for_extraction
type suite_buff = lbuffer uint8 1ul

/// -------------------------
/// Party state
/// -------------------------

/// Low-level model of Party's state, keep track of party-specific fields on agreed-cipherSuite
type party_state_mem (#cs:SpecCrypto.supported_cipherSuite)
  = suite_buff
  & ec_keypair_mem #cs
  & ecdsa_sig_keypair_mem #cs
  & id_cred_buff
  & opt_ec_keypair_mem #cs // optional type, component could be NULL
  & ec_pub_key_buf cs
  & ecdsa_pub_key_buf cs
  & id_cred_buff

/// getters
let ps_mem_get_suite_i (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> suite_buff

let ps_mem_get_static_dh_kp (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> static_dh_keypair_mem

let ps_mem_get_sig_kp (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> sig_keypair_mem

let ps_mem_get_id_cred (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> id_buff

let ps_mem_get_eph_keypair (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> eph_ec_keypair_mem

let ps_mem_get_remote_static_pub (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> remote_stat_pub_buff

let ps_mem_get_remote_sig_pub (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> remote_sig_pub_buff

let ps_mem_get_remote_id_cred (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> remote_id_cred_buff

inline_for_extraction noextract
let g_is_null_ps_eph_keypair (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = (g_is_null_opt_ec_keypair_mem (ps_mem_get_eph_keypair ps_mem))

/// Predicates for memory reasoning
let party_state_mem_live (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> (
      live h suite_buff /\ ec_keypair_mem_live h static_dh_keypair_mem
      /\ ecdsa_sig_keypair_mem_live h sig_keypair_mem /\ live h id_buff
      /\ opt_ec_keypair_mem_live h eph_ec_keypair_mem /\ live h remote_stat_pub_buff
      /\ live h remote_sig_pub_buff /\ live h remote_id_cred_buff
    )

let lemma_party_state_mem_live (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (ps_mem:party_state_mem #cs)
  : Lemma (ensures 
    party_state_mem_live h ps_mem ==> (
      let sig_keypair = ps_mem_get_sig_kp ps_mem in
      let static_dh_keypair = ps_mem_get_static_dh_kp ps_mem in
      live h (ecdsa_sig_keypair_mem_get_priv sig_keypair) /\ live h (ecdsa_sig_keypair_mem_get_pub sig_keypair)
      /\ live h (ec_keypair_mem_get_priv static_dh_keypair) /\ live h (ec_keypair_mem_get_pub static_dh_keypair)
    )
  )
  [SMTPat (party_state_mem_live #cs h ps_mem)]
  = ()

let party_state_mem_disjoint (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> (
      B.all_disjoint [loc suite_buff; ec_keypair_mem_union_loc static_dh_keypair_mem;
          ecdsa_sig_keypair_mem_union_loc sig_keypair_mem; loc id_buff;
          opt_ec_keypair_mem_union_loc eph_ec_keypair_mem; loc remote_stat_pub_buff;
          loc remote_sig_pub_buff; loc remote_id_cred_buff
      ]
    )

let party_state_mem_union_loc (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> (
      B.loc_union (B.loc_union (loc suite_buff)
      (B.loc_union (ec_keypair_mem_union_loc static_dh_keypair_mem)
      (B.loc_union (ecdsa_sig_keypair_mem_union_loc sig_keypair_mem)
      (B.loc_union (loc id_buff)
      (B.loc_union (opt_ec_keypair_mem_union_loc eph_ec_keypair_mem)
      (B.loc_union (loc remote_stat_pub_buff)
      (loc remote_sig_pub_buff)))))))
      (loc remote_id_cred_buff)
    )

let modifies_ps_mem (#cs:SpecCrypto.supported_cipherSuite)
  (ps_m:party_state_mem #cs) (h0 h1:HS.mem)
  = modifies (party_state_mem_union_loc ps_m) h0 h1

let party_state_mem_disjoint_to (#cs:SpecCrypto.supported_cipherSuite)
  (#t2:buftype) (#a2:Type0) (ps_mem:party_state_mem #cs)
  (b2:buffer_t t2 a2)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> (
    disjoint suite_buff b2 /\ ec_keypair_mem_disjoint_to static_dh_keypair_mem b2
    /\ ecdsa_sig_keypair_mem_disjoint_to sig_keypair_mem b2 /\ disjoint id_buff b2
    /\ opt_ec_keypair_mem_disjoint_to eph_ec_keypair_mem b2 /\ disjoint remote_stat_pub_buff b2
    /\ disjoint remote_sig_pub_buff b2 /\ disjoint remote_id_cred_buff b2
  )


let party_state_mem_disjoint_to_msg1_m (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs) (msg1_m:message1_mem #cs)
  = match msg1_m with method_m, suite_m, epub_m, c_id_m, ead1_m -> (
    party_state_mem_disjoint_to ps_mem method_m
    /\ party_state_mem_disjoint_to ps_mem suite_m
    /\ party_state_mem_disjoint_to ps_mem epub_m
    /\ party_state_mem_disjoint_to ps_mem c_id_m
    /\ party_state_mem_disjoint_to ps_mem ead1_m
  )

let lemma_party_state_mem_disjoint_to_msg1_m (#cs:SpecCrypto.supported_cipherSuite)
  (ps_mem:party_state_mem #cs) (msg1_m:message1_mem #cs)
  : Lemma (ensures (
    let g_x = message1_mem_get_g_x msg1_m in
    let epub_m = opt_ec_keypair_mem_get_pub (ps_mem_get_eph_keypair ps_mem) in

    party_state_mem_disjoint_to_msg1_m ps_mem msg1_m ==> B.loc_disjoint (loc g_x) (loc epub_m)
  ))
  [SMTPat (party_state_mem_disjoint_to_msg1_m #cs ps_mem msg1_m)]
  = ()

inline_for_extraction
let is_valid_party_state_mem (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (ps_mem:party_state_mem #cs)
  = party_state_mem_live h ps_mem /\ party_state_mem_disjoint ps_mem

/// Refinement types of `party_state_mem`
let is_legit_party_state_mem (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (ps_mem:party_state_mem #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> (
      let suite_label = uint_to_nat (bget h suite_buff 0) in
      suite_label >=6 /\ suite_label <= 7
    )

inline_for_extraction
type legit_party_state_mem (#cs:SpecCrypto.supported_cipherSuite) (h:HS.mem)
  = ps_mem:party_state_mem #cs{is_legit_party_state_mem h ps_mem}

inline_for_extraction
type party_state_mem_shared_est (#cs:SpecCrypto.supported_cipherSuite)
  = ps_mem:party_state_mem #cs{
    match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> (
      not (g_is_null_opt_ec_keypair_mem eph_ec_keypair_mem)
    )
  }
 
/// Convert computational model to abstract model of `party_state`
let eval_party_state_mem (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (ps_mem:legit_party_state_mem #cs h)
  : GTot (Spec.party_state #cs)
  = match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> (
      let suite_label = uint_to_nat (bget h suite_buff 0) in
      {
        suites = suite_label;
        static_dh = eval_ec_keypair_mem h static_dh_keypair_mem;
        signature_key = eval_ecdsa_sig_keypair_mem h sig_keypair_mem;
        id_cred = as_seq h id_buff;
        eph_ec_keypair = eval_opt_ec_keypair_mem h eph_ec_keypair_mem;
        remote_static_pub_key = as_seq h remote_stat_pub_buff;
        remote_signature_pub_key = as_seq h remote_sig_pub_buff;
        remote_id_cred = as_seq h remote_id_cred_buff
      }
    )

let lemma_eval_party_state_mem (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (ps_mem:legit_party_state_mem #cs h)
  : Lemma (ensures (
    let ps_abstract = eval_party_state_mem h ps_mem in
    match ps_mem with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> (
      let opt_eph_ec_keypair = eval_opt_ec_keypair_mem h eph_ec_keypair_mem in

      ps_abstract.suites = uint_to_nat (bget h suite_buff 0)
      /\ is_equiv_ec_keypair_mem h static_dh_keypair_mem ps_abstract.static_dh
      /\ is_equiv_ecdsa_sig_keypair_mem h sig_keypair_mem ps_abstract.signature_key
      /\ Seq.equal ps_abstract.id_cred (as_seq h id_buff)
      /\ Some? ps_abstract.eph_ec_keypair <==> Some? opt_eph_ec_keypair
      /\ (Some? ps_abstract.eph_ec_keypair ==> (
        let ephe_ec_keypair_v = Some?.v ps_abstract.eph_ec_keypair in
        let opt_eph_ec_keypair_v = Some?.v opt_eph_ec_keypair in
        Seq.equal ephe_ec_keypair_v.pub opt_eph_ec_keypair_v.pub
        /\ Seq.equal ephe_ec_keypair_v.priv opt_eph_ec_keypair_v.priv
      ))
      /\ Seq.equal ps_abstract.remote_static_pub_key (as_seq h remote_stat_pub_buff)
      /\ Seq.equal ps_abstract.remote_signature_pub_key (as_seq h remote_sig_pub_buff)
      /\ Seq.equal ps_abstract.remote_id_cred (as_seq h remote_id_cred_buff)
    )
  ))
  [SMTPat (eval_party_state_mem #cs h ps_mem)]
  = ()

let lemma_eval_party_state_mem_shared_est (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (ps_mem:party_state_mem_shared_est #cs)
  : Lemma (requires is_legit_party_state_mem h ps_mem)
  (ensures (
    let ps_abstract = eval_party_state_mem h ps_mem in
    Some? ps_abstract.eph_ec_keypair
  ))
  [SMTPat (eval_party_state_mem #cs h ps_mem)]
  = ()

/// getters for `party_state_mem`
inline_for_extraction noextract
let party_state_mem_get_shared_key (#cs:SpecCrypto.supported_cipherSuite)
  (ps_m:party_state_mem #cs)
  = match ps_m with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> eph_ec_keypair_mem

inline_for_extraction noextract
let party_state_mem_get_suite (#cs:SpecCrypto.supported_cipherSuite)
  (ps_m:party_state_mem #cs)
  = match ps_m with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> suite_buff

inline_for_extraction noextract
let party_state_mem_get_static_dh_kp (#cs:SpecCrypto.supported_cipherSuite)
  (ps_m:party_state_mem #cs)
  = match ps_m with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> static_dh_keypair_mem

inline_for_extraction noextract
let party_state_mem_get_sig_kp (#cs:SpecCrypto.supported_cipherSuite)
  (ps_m:party_state_mem #cs)
  = match ps_m with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> sig_keypair_mem

inline_for_extraction noextract
let party_state_mem_get_id (#cs:SpecCrypto.supported_cipherSuite)
  (ps_m:party_state_mem #cs)
  = match ps_m with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_cred_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> id_cred_buff

inline_for_extraction noextract
let party_state_mem_get_remote_stat_pub (#cs:SpecCrypto.supported_cipherSuite)
  (ps_m:party_state_mem #cs)
  = match ps_m with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> remote_stat_pub_buff

inline_for_extraction noextract
let party_state_mem_get_remote_sig_pub (#cs:SpecCrypto.supported_cipherSuite)
  (ps_m:party_state_mem #cs)
  = match ps_m with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> remote_sig_pub_buff

inline_for_extraction noextract
let party_state_mem_get_remote_id_cred (#cs:SpecCrypto.supported_cipherSuite)
  (ps_m:party_state_mem #cs)
  = match ps_m with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> remote_id_cred_buff

/// update function for `party_state_mem`,
/// used for updating the [eph_ec_keypair] field
inline_for_extraction noextract
val update_ps_mem_shared_key:
  #cs:SpecCrypto.supported_cipherSuite
  -> eph_keypair:opt_ec_keypair_mem #cs
  -> ps_m:party_state_mem #cs
  -> ST.Stack unit
  (requires fun h0 -> (
    let src_priv = opt_ec_keypair_mem_get_priv eph_keypair in
    let dst_keypair = (party_state_mem_get_shared_key ps_m) in
    is_valid_party_state_mem h0 ps_m /\ is_valid_opt_ec_keypair_mem h0 eph_keypair
    /\ is_valid_opt_ec_keypair_mem h0 dst_keypair
    /\ B.loc_disjoint (party_state_mem_union_loc ps_m) (opt_ec_keypair_mem_union_loc eph_keypair)
    /\ g_is_same_state_opt_ec_keypair_mem eph_keypair
    /\ g_is_same_state_opt_ec_keypair_mem dst_keypair
    /\ (g_is_null_opt_ec_keypair_mem eph_keypair <==> g_is_null_opt_ec_keypair_mem dst_keypair)
    // /\ (g_is_null_opt_ec_keypair_mem dst_keypair ==> g_is_null src_priv)
  ))
  (ensures fun h0 _ h1 -> (
    if (g_is_null_opt_ec_keypair_mem eph_keypair) then modifies0 h0 h1
    else (
      let opt_shared_keypair:opt_ec_keypair_mem #cs = party_state_mem_get_shared_key ps_m in
      modifies (opt_ec_keypair_mem_union_loc opt_shared_keypair) h0 h1
      /\ (match eph_keypair with src_pub, src_priv ->
          match opt_shared_keypair with dst_pub, dst_priv ->
            Seq.equal (nn_as_seq h0 src_pub) (nn_as_seq h1 dst_pub)
            /\ Seq.equal (nn_as_seq h0 src_priv) (nn_as_seq h1 dst_priv)
      )
    )
  ))
    
/// -------------------------
/// Handshake state
/// -------------------------
inline_for_extraction
noeq type hs_mem (#cs:SpecCrypto.supported_cipherSuite)
  = {
    suite_i: suite_buff;
    method: lbuffer uint8 1ul;
    g_x: ec_pub_key_buf cs;
    msg1_hash: hash_out_buff cs;
    g_y: ec_pub_key_buf cs;
    g_xy: shared_secret_buf cs;
    g_rx: opt_shared_secret_buf cs;
    g_iy: opt_shared_secret_buf cs;
    th2: hash_out_buff cs;
    th3: hash_out_buff cs;
    th4: hash_out_buff cs;
    prk2e: hash_out_buff cs;
    prk3e2m: hash_out_buff cs;
    prk4e3m: hash_out_buff cs;
    prk_out: hash_out_buff cs;
    prk_exporter: hash_out_buff cs;
  }

inline_for_extraction
type hs_mem_after_msg1 (#cs:SpecCrypto.supported_cipherSuite)
  = hs_m:hs_mem #cs{True}

inline_for_extraction
type hs_mem_after_msg2 (#cs:SpecCrypto.supported_cipherSuite)
  = hs_m:hs_mem_after_msg1 #cs {
    ~(g_is_null hs_m.th2)
    /\ ~(g_is_null hs_m.g_y) /\ ~(g_is_null hs_m.g_xy)
    /\ ~(g_is_null hs_m.prk3e2m) /\ ~(g_is_null hs_m.prk2e)
  }

inline_for_extraction
type hs_mem_after_msg3 (#cs:SpecCrypto.supported_cipherSuite)
  = hs_m:hs_mem_after_msg2 #cs {
    ~(g_is_null hs_m.th3) /\ ~(g_is_null hs_m.th4)
    /\ ~(g_is_null hs_m.prk4e3m) /\ ~(g_is_null hs_m.prk_out)
    /\ ~(g_is_null hs_m.prk_exporter)
  }

/// Predicates for `hs_mem`
let hs_mem_live (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (hs_m:hs_mem #cs)
  = live h hs_m.suite_i /\ live h hs_m.method /\ live h hs_m.g_x
  /\ live h hs_m.msg1_hash /\ live h hs_m.g_y /\ live h hs_m.g_xy
  /\ live h hs_m.g_rx /\ live h hs_m.g_iy /\ live h hs_m.th2
  /\ live h hs_m.th3 /\ live h hs_m.th4 /\ live h hs_m.prk2e
  /\ live h hs_m.prk3e2m /\ live h hs_m.prk4e3m /\ live h hs_m.prk_out
  /\ live h hs_m.prk_exporter

let hs_mem_disjoint (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs)
  = B.all_disjoint [loc hs_m.suite_i; loc hs_m.method; loc hs_m.g_x;
                    loc hs_m.msg1_hash; loc hs_m.g_y; loc hs_m.g_xy;
                    loc hs_m.g_rx; loc hs_m.g_iy; loc hs_m.th2;
                    loc hs_m.th3; loc hs_m.th4; loc hs_m.prk2e;
                    loc hs_m.prk3e2m; loc hs_m.prk4e3m; loc hs_m.prk_out;
                    loc hs_m.prk_exporter]

let is_valid_hs_mem (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (hs_m:hs_mem #cs)
  = hs_mem_live h hs_m /\ hs_mem_disjoint hs_m

let hs_mem_union_loc (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs)
  = B.loc_union (B.loc_union (loc hs_m.suite_i)
  (B.loc_union (loc hs_m.method)
  (B.loc_union (loc hs_m.g_x)
  (B.loc_union (loc hs_m.msg1_hash)
  (B.loc_union (loc hs_m.g_y)
  (B.loc_union (loc hs_m.g_xy)
  (B.loc_union (loc hs_m.g_rx)
  (B.loc_union (loc hs_m.g_iy)
  (B.loc_union (loc hs_m.th2)
  (B.loc_union (loc hs_m.th3)
  (B.loc_union (loc hs_m.th4)
  (B.loc_union (loc hs_m.prk2e)
  (B.loc_union (loc hs_m.prk3e2m)
  (B.loc_union (loc hs_m.prk4e3m)
  (loc hs_m.prk_out)))))))))))))))
  (loc hs_m.prk_exporter)

let modifies_hs_mem (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs) (h0 h1:HS.mem)
  = modifies (hs_mem_union_loc hs_m) h0 h1

inline_for_extraction noextract
let hs_mem_disjoint_to (#t2:buftype) (#a2:Type0)
  (#cs:SpecCrypto.supported_cipherSuite) (hs_m:hs_mem #cs)
  (b2:buffer_t t2 a2)
  = B.loc_disjoint (hs_mem_union_loc hs_m) (loc b2)

let lemma_hs_mem_disjoint_to (#t2:buftype) (#a2:Type0)
  (#cs:SpecCrypto.supported_cipherSuite) (hs_m:hs_mem #cs)
  (b2:buffer_t t2 a2)
  : Lemma (ensures (
    hs_mem_disjoint_to hs_m b2 ==> (
      disjoint b2 (hs_m.g_rx) /\ disjoint b2 hs_m.g_xy
      /\ disjoint b2 hs_m.suite_i /\ disjoint b2 hs_m.method
      /\ disjoint b2 hs_m.g_x
      /\ disjoint b2 hs_m.msg1_hash /\ disjoint b2 hs_m.g_y
      /\ disjoint b2 hs_m.g_iy /\ disjoint b2 hs_m.th2
      /\ disjoint b2 hs_m.th3 /\ disjoint b2 hs_m.th3
      /\ disjoint b2 hs_m.th4 /\ disjoint b2 hs_m.prk2e
      /\ disjoint b2 hs_m.prk3e2m /\ disjoint b2 hs_m.prk4e3m
      /\ disjoint b2 hs_m.prk_out /\ disjoint b2 hs_m.prk_exporter
    )
  ))
  [SMTPat (hs_mem_disjoint_to #t2 #a2 #cs hs_m b2)]
  = ()

let hs_mem_disjoint_to_ps_mem (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs) (ps_m:party_state_mem #cs)
  = B.loc_disjoint (hs_mem_union_loc hs_m) (party_state_mem_union_loc ps_m)

let lemma_hs_mem_disjoint_to_ps_mem (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs) (ps_m:party_state_mem #cs)
  : Lemma (ensures (
    let epub_m = opt_ec_keypair_mem_get_pub (ps_mem_get_eph_keypair ps_m) in
    hs_mem_disjoint_to_ps_mem hs_m ps_m ==> (
      match ps_m with suite_buff, static_dh_keypair_mem, sig_keypair_mem, id_buff,
                      eph_ec_keypair_mem, remote_stat_pub_buff, remote_sig_pub_buff,
                      remote_id_cred_buff -> (
        
        hs_mem_disjoint_to hs_m suite_buff /\
        (match static_dh_keypair_mem with pub, priv -> hs_mem_disjoint_to hs_m pub
                                                      /\ hs_mem_disjoint_to hs_m priv)
        /\ (match sig_keypair_mem with pub, priv -> hs_mem_disjoint_to hs_m pub
                                                      /\ hs_mem_disjoint_to hs_m priv)
        /\ hs_mem_disjoint_to hs_m id_buff
        /\ (match eph_ec_keypair_mem with pub, priv -> hs_mem_disjoint_to hs_m pub
                                                      /\ hs_mem_disjoint_to hs_m priv)
        /\ hs_mem_disjoint_to hs_m remote_stat_pub_buff
        /\ hs_mem_disjoint_to hs_m remote_sig_pub_buff
        /\ hs_mem_disjoint_to hs_m remote_id_cred_buff
      )
    )
  ))
  [SMTPat (hs_mem_disjoint_to_ps_mem #cs hs_m ps_m)]
  = ()

let hs_mem_disjoint_to_msg1_m (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs) (msg1_m:message1_mem #cs)
  = B.loc_disjoint (hs_mem_union_loc hs_m) (message1_mem_union_loc msg1_m)

let is_legit_hs_mem (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (hs_m:hs_mem #cs)
  = let suite_label = uint_to_nat (bget h hs_m.suite_i 0) in
  let method_label = uint_to_nat (bget h hs_m.method 0) in
  suite_label >=6 /\ suite_label <= 7
  /\ method_label > 0 /\ method_label <= 4

/// Modifies clauses
let hs_mem_modifies (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs) (h0 h1:HS.mem)
  = modifies (hs_mem_union_loc hs_m) h0 h1

let hs_mem_modifies_with (#cs:SpecCrypto.supported_cipherSuite)
  (hs_m:hs_mem #cs) (#a:Type0) (b:buffer_t MUT a) (h0 h1:HS.mem)
  = modifies (B.loc_union (hs_mem_union_loc hs_m) (loc b)) h0 h1

/// Conversion between computational model and abstract model
/// of `handshake_state`
let eval_hs_mem (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (hs_m:hs_mem #cs{is_legit_hs_mem #cs h hs_m})
  : GTot (Spec.handshake_state #cs)
  = {
    suite_i = uint_to_nat (bget h hs_m.suite_i 0);
    method = label_to_method (uint_to_nat (bget h hs_m.method 0));
    g_x = as_seq h hs_m.g_x;
    msg1_hash = as_seq h hs_m.msg1_hash;
    // g_y = lbuffer_or_null_as_seq h hs_m.g_y;
    g_y = Some (as_seq h hs_m.g_y);
    g_xy = Some (as_seq h hs_m.g_xy);
    g_rx = lbuffer_or_null_as_seq h hs_m.g_rx;
    g_iy = lbuffer_or_null_as_seq h hs_m.g_iy;
    th2 = Some (as_seq h hs_m.th2);
    th3 = Some (as_seq h hs_m.th3);
    th4 = Some (as_seq h hs_m.th4);
    prk2e = Some (as_seq h hs_m.prk2e);
    prk3e2m = Some (as_seq h hs_m.prk3e2m);
    prk4e3m = Some (as_seq h hs_m.prk4e3m);
    prk_out = Some (as_seq h hs_m.prk_out);
    prk_exporter = Some (as_seq h hs_m.prk_exporter)
  }

let lemma_eval_hs_mem_equiv (#cs:SpecCrypto.supported_cipherSuite)
  (h:HS.mem) (hs_m:hs_mem #cs{is_legit_hs_mem #cs h hs_m})
  : Lemma (ensures (
    let hs_abstract = eval_hs_mem #cs h hs_m in

    // (Some? hs_abstract.g_y <==> ~(g_is_null hs_m.g_y))
    // /\ (Some? hs_abstract.g_xy <==> ~(g_is_null hs_m.g_xy) )
    
    (Some? hs_abstract.g_rx <==> ~(g_is_null hs_m.g_rx))
    /\ (Some? hs_abstract.g_iy <==> ~(g_is_null hs_m.g_iy))

    // /\ (Some? hs_abstract.th2 <==> ~(g_is_null hs_m.th2))
    // /\ (Some? hs_abstract.th3 <==> ~(g_is_null hs_m.th3))
    // /\ (Some? hs_abstract.th4 <==> ~(g_is_null hs_m.th4))
    // /\ (Some? hs_abstract.prk2e <==> ~(g_is_null hs_m.prk2e))
    // /\ (Some? hs_abstract.prk3e2m <==> ~(g_is_null hs_m.prk3e2m))
    // /\ (Some? hs_abstract.prk4e3m <==> ~(g_is_null hs_m.prk4e3m))
    // /\ (Some? hs_abstract.prk_out <==> ~(g_is_null hs_m.prk_out))
    // /\ (Some? hs_abstract.prk_exporter <==> ~(g_is_null hs_m.prk_exporter))
  ))
  [SMTPat (eval_hs_mem #cs h hs_m)]
  = ()
