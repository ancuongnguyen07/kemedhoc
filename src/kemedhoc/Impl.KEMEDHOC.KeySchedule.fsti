module Impl.KEMEDHOC.KeySchedule

(*HACL related modules*)
// open Lib.RawIntTypes
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

open Impl.EDHOC.Utilities

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module Spec = Spec.KEMEDHOC.KeySchedule

module FBytes = FStar.Bytes

(*EDHOC utilities*)
module SpecEdhocSerd = Spec.EDHOC.Serialization
module SpecEdhocParser = Spec.EDHOC.Parser
module TypeHelper = TypeHelper.EDHOC

(*KEMEDHOC libraries*)
open Impl.KEMEDHOC.CryptoPrimitives
open Impl.KEMEDHOC.Parser
open Impl.KEMEDHOC.Types
module SpecParser = Spec.KEMEDHOC.Parser
module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives

(*---------------------------- HKDF Info*)
unopteq type info = {
    label: lbuffer uint8 1ul;
    context: serializable_buff;
    okm_len: TypeHelper.okm_len_type_buff;
}

let info_live (h: HS.mem) (i: info)
    = live h i.label /\ live h i.context /\ live h i.okm_len

let info_disjoint (i: info)
    = B.all_disjoint [loc i.label; loc i.context; loc i.okm_len]

let is_legit_info (h: HS.mem) (i: info)
    = SpecEdhocSerd.bytes_to_nat (as_seq h i.label) <= 13
    /\ SpecEdhocSerd.bytes_to_nat (as_seq_buff h i.okm_len) <= SpecEdhocParser.okm_len_max_size

inline_for_extraction
type legitInfo (h: HS.mem) = i: info{is_legit_info h i}

let is_valid_info (h: HS.mem) (i: info)
    = info_live h i /\ info_disjoint i
    /\ is_legit_info h i

let info_eval (h: HS.mem) (i: legitInfo h)
    : GTot Spec.info
    = {
        label = SpecEdhocSerd.bytes_to_nat (as_seq h i.label);
        context = as_seq_buff h i.context;
        okm_len = SpecEdhocSerd.bytes_to_nat (as_seq_buff h i.okm_len);
    }

let info_union (i: info)
    = loc i.label |+| loc i.context |+| loc i.okm_len

let construct_info (label: lbuffer uint8 1ul)
    (context: serializable_buff) (okm_len: TypeHelper.okm_len_type_buff)
    : info
    = { label = label; context = context; okm_len = okm_len }

inline_for_extraction
let concat_info_get_length (i: info)
    : GTot size_t
    = 1ul +! size (length i.context) +! size (length i.okm_len)

val concat_info:
    i: info
    -> context_len: size_t
    -> okm_len: size_t{size_v okm_len <= 2}
    -> i_buffer: lbuffer uint8 (concat_info_get_length i)
    -> ST.Stack unit
    (requires fun h0 -> (1 + size_v context_len + size_v okm_len = size_v (concat_info_get_length i))
        /\ (length i.context = size_v context_len)
        /\ (length i.okm_len = size_v okm_len)
        /\ is_valid_info h0 i /\ live h0 i_buffer
        /\ B.loc_disjoint (loc i_buffer) (info_union i)
    )
    (ensures fun h0 _ h1 ->
        let concatenated_info_s = Spec.concat_info (info_eval h0 i) in

        modifies1 i_buffer h0 h1
        /\ Seq.equal (as_seq h1 i_buffer) concatenated_info_s
    )


(*---------------------------- HKDF context*)

/// ---------------
/// Context 2
/// ---------------
unopteq type context2 (kcs: supportedKemCipherSuite) = {
    c_r: c_id_buffer;
    id_cred_r: id_cred_buffer;
    th2: hash_out_buff kcs;
    cred_r: cred_buffer;
    // Does not support EAD2
}

let context2_live (#kcs: supportedKemCipherSuite) (h: HS.mem) (ctx2: context2 kcs)
    = live h ctx2.c_r /\ live h ctx2.id_cred_r
    /\ live h ctx2.th2 /\ live h ctx2.cred_r

let context2_disjoint (#kcs: supportedKemCipherSuite) (ctx2: context2 kcs)
    = B.all_disjoint [loc ctx2.c_r; loc ctx2.id_cred_r; loc ctx2.th2; loc ctx2.cred_r]

let is_valid_context2 (#kcs: supportedKemCipherSuite) (h: HS.mem) (ctx2: context2 kcs)
    = context2_live h ctx2 /\ context2_disjoint ctx2

let context2_union (#kcs: supportedKemCipherSuite) (ctx2: context2 kcs)
    = loc ctx2.c_r |+| loc ctx2.id_cred_r
      |+| loc ctx2.th2 |+| loc ctx2.cred_r

let context2_eval (#kcs: supportedKemCipherSuite) (h: HS.mem) (ctx2: context2 kcs)
    : GTot (Spec.context2 #kcs)
    = {
        c_r = as_seq h ctx2.c_r;
        id_cred_r = as_seq h ctx2.id_cred_r;
        th2 = as_seq h ctx2.th2;
        cred_r = as_seq h ctx2.cred_r;
    }

inline_for_extraction
let concat_context2_get_fixed_length (kcs: supportedKemCipherSuite)
    = size SpecParser.c_id_size +! size SpecParser.id_cred_size
      +! size (SpecCrypto.hash_size kcs) +! size SpecParser.cred_size

val concat_context2:
    #kcs: supportedKemCipherSuite
    -> ctx2: context2 kcs
    -> ctx2_buffer: lbuffer uint8 (concat_context2_get_fixed_length kcs)
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_context2 h0 ctx2 /\ live h0 ctx2_buffer
        /\ B.loc_disjoint (loc ctx2_buffer) (context2_union ctx2)
    )
    (ensures fun h0 _ h1 ->
        let concatenated_ctx2_s = Spec.concat_context2 #kcs (context2_eval h0 ctx2) in
        
        modifies1 ctx2_buffer h0 h1
        /\ Seq.equal (as_seq h1 ctx2_buffer) concatenated_ctx2_s
    )

/// ---------------
/// Context 3
/// ---------------
unopteq type context3 (kcs: supportedKemCipherSuite) = {
    id_cred_i: id_cred_buffer;
    th3: hash_out_buff kcs;
    cred_i: cred_buffer;
    // Does not support EAD3
}

let context3_live (#kcs: supportedKemCipherSuite) (h: HS.mem) (ctx3: context3 kcs)
    = live h ctx3.id_cred_i /\ live h ctx3.th3 /\ live h ctx3.cred_i

let context3_disjoint (#kcs: supportedKemCipherSuite) (ctx3: context3 kcs)
    = B.all_disjoint [loc ctx3.id_cred_i; loc ctx3.th3; loc ctx3.cred_i]

let is_valid_context3 (#kcs: supportedKemCipherSuite) (h: HS.mem) (ctx3: context3 kcs)
    = context3_live h ctx3 /\ context3_disjoint ctx3

let context3_eval (#kcs: supportedKemCipherSuite) (h: HS.mem) (ctx3: context3 kcs)
    : GTot (Spec.context3 #kcs)
    = {
        id_cred_i = as_seq h ctx3.id_cred_i;
        th3 = as_seq h ctx3.th3;
        cred_i = as_seq h ctx3.cred_i;
    }

let context3_union (#kcs: supportedKemCipherSuite) (ctx3: context3 kcs)
    = loc ctx3.id_cred_i |+| loc ctx3.th3 |+| loc ctx3.cred_i

let concat_context3_get_fixed_length (kcs: supportedKemCipherSuite)
    = size SpecParser.id_cred_size +! size (SpecCrypto.hash_size kcs)
      +! size SpecParser.cred_size

val concat_context3:
    #kcs: supportedKemCipherSuite
    -> ctx3: context3 kcs
    -> ctx3_buffer: lbuffer uint8 (concat_context3_get_fixed_length kcs)
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_context3 h0 ctx3 /\ live h0 ctx3_buffer
        /\ B.loc_disjoint (loc ctx3_buffer) (context3_union ctx3)
    )
    (ensures fun h0 _ h1 ->
        let concatenated_ctx3_s = Spec.concat_context3 #kcs (context3_eval h0 ctx3) in

        modifies1 ctx3_buffer h0 h1
        /\ Seq.equal (as_seq h1 ctx3_buffer) concatenated_ctx3_s
    )

(*---------------------------- HKDF key schedule*)

/// ---------------
/// PRK
/// ---------------
val extract_prk1e:
    #kcs: supportedKemCipherSuite
    -> th1: hash_out_buff kcs // salt
    -> k_auth_R: kem_shared_secret_buff kcs // ikm
    -> prk1e: hash_out_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 th1 /\ live h0 k_auth_R /\ live h0 prk1e
        /\ B.all_disjoint [loc th1; loc k_auth_R; loc prk1e]
    )
    (ensures fun h0 _ h1 ->
        let prk1e_s = Spec.extract_prk1e #kcs (as_seq h0 th1) (as_seq h0 k_auth_R) in
        
        modifies1 prk1e h0 h1
        /\ Seq.equal (as_seq h1 prk1e) prk1e_s
    )

val extract_prk2e:
    #kcs: supportedKemCipherSuite
    -> prk1e: hash_out_buff kcs
    -> th2: hash_out_buff kcs // salt = H(prk1e || th2)
    -> k_xy: kem_shared_secret_buff kcs // ikm
    -> prk2e: hash_out_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 prk1e /\ live h0 th2 /\ live h0 k_xy /\ live h0 prk2e
        /\ B.all_disjoint [loc prk1e; loc th2; loc k_xy; loc prk2e]
    )
    (ensures fun h0 _ h1 ->
        let prk2e_s = Spec.extract_prk2e #kcs (as_seq h0 prk1e) (as_seq h0 th2) (as_seq h0 k_xy) in

        modifies1 prk2e h0 h1
        /\ Seq.equal (as_seq h1 prk2e) prk2e_s
    )

val extract_prk3e2m:
    #kcs: supportedKemCipherSuite
    -> salt3e2m: hash_out_buff kcs // salt
    -> k_auth_R: kem_shared_secret_buff kcs // ikm
    -> prk3e2m: hash_out_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 salt3e2m /\ live h0 k_auth_R /\ live h0 prk3e2m
        /\ B.all_disjoint [loc salt3e2m; loc k_auth_R; loc prk3e2m]
    )
    (ensures fun h0 _ h1 ->
        let prk3e2m_s = Spec.extract_prk3e2m #kcs (as_seq h0 salt3e2m) (as_seq h0 k_auth_R) in

        modifies1 prk3e2m h0 h1
        /\ Seq.equal (as_seq h1 prk3e2m) prk3e2m_s
    )

val extract_prk4e3m:
    #kcs: supportedKemCipherSuite
    -> salt4e3m: hash_out_buff kcs // salt
    -> k_auth_I: kem_shared_secret_buff kcs // ikm
    -> prk4e3m: hash_out_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 salt4e3m /\ live h0 k_auth_I /\ live h0 prk4e3m
        /\ B.all_disjoint [loc salt4e3m; loc k_auth_I; loc prk4e3m]
    )
    (ensures fun h0 _ h1 ->
        let prk4e3m_s = Spec.extract_prk4e3m #kcs (as_seq h0 salt4e3m) (as_seq h0 k_auth_I) in

        modifies1 prk4e3m h0 h1
        /\ Seq.equal (as_seq h1 prk4e3m) prk4e3m_s
    )

val expand_prk_out:
    #kcs: supportedKemCipherSuite
    -> prk4e3m: hash_out_buff kcs
    -> th4: hash_out_buff kcs
    -> prk_out: hash_out_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 prk4e3m /\ live h0 th4 /\ live h0 prk_out
        /\ B.all_disjoint [loc prk4e3m; loc th4; loc prk_out]
    )
    (ensures fun h0 _ h1 ->
        let prk_out_s = Spec.expand_prk_out #kcs (as_seq h0 prk4e3m) (as_seq h0 th4) in

        modifies1 prk_out h0 h1
        /\ Seq.equal (as_seq h1 prk_out) prk_out_s
    )

val expand_prk_exporter:
    #kcs: supportedKemCipherSuite
    -> prk_out: hash_out_buff kcs
    -> prk_exporter: hash_out_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 prk_out /\ live h0 prk_exporter
        /\ B.all_disjoint [loc prk_out; loc prk_exporter]
    )
    (ensures fun h0 _ h1 ->
        let prk_exporter_s = Spec.expand_prk_exporter #kcs (as_seq h0 prk_out) in

        modifies1 prk_exporter h0 h1
        /\ Seq.equal (as_seq h1 prk_exporter) prk_exporter_s
    )

/// ---------------
/// Encryption Key
/// ---------------
val expand_k:
    #kcs: supportedKemCipherSuite
    -> key_label: nat{key_label <= 13}
    -> prk: hash_out_buff kcs
    -> th: hash_out_buff kcs
    -> k: aead_key_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 prk /\ live h0 th /\ live h0 k
        /\ B.all_disjoint [loc prk; loc th; loc k]
    )
    (ensures fun h0 _ h1 ->
        let k_s = Spec.expand_k #kcs key_label (as_seq h0 prk) (as_seq h0 th) in

        modifies1 k h0 h1
        /\ Seq.equal (as_seq h1 k) k_s
    )

/// ---------------
/// Initial Vector
/// ---------------
val expand_iv:
    #kcs: supportedKemCipherSuite
    -> iv_label: nat{iv_label <= 13}
    -> prk: hash_out_buff kcs
    -> th: hash_out_buff kcs
    -> iv: aead_iv_buff
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 prk /\ live h0 th /\ live h0 iv
        /\ B.all_disjoint [loc prk; loc th; loc iv]
    )
    (ensures fun h0 _ h1 ->
        let iv_s = Spec.expand_iv #kcs iv_label (as_seq h0 prk) (as_seq h0 th) in

        modifies1 iv h0 h1
        /\ Seq.equal (as_seq h1 iv) iv_s
    )

/// ---------------
/// SALT
/// ---------------
val expand_salt:
    #kcs: supportedKemCipherSuite
    -> salt_label: nat{salt_label <= 13}
    -> prk: hash_out_buff kcs
    -> th: hash_out_buff kcs
    -> salt: hash_out_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 prk /\ live h0 th /\ live h0 salt
        /\ B.all_disjoint [loc prk; loc th; loc salt]
    )
    (ensures fun h0 _ h1 ->
        let salt_s = Spec.expand_salt #kcs salt_label (as_seq h0 prk) (as_seq h0 th) in

        modifies1 salt h0 h1
        /\ Seq.equal (as_seq h1 salt) salt_s
    )

/// ---------------
/// MAC
/// ---------------
val expand_mac2:
    #kcs: supportedKemCipherSuite
    -> prk3e2m: hash_out_buff kcs
    -> ctx2: context2 kcs
    -> mac2: mac23_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_context2 h0 ctx2 /\ live h0 prk3e2m /\ live h0 mac2
        /\ B.all_disjoint [loc prk3e2m; context2_union ctx2; loc mac2]
    )
    (ensures fun h0 _ h1 ->
        let mac2_s = Spec.expand_mac2 #kcs (as_seq h0 prk3e2m) (context2_eval h0 ctx2) in

        modifies1 mac2 h0 h1
        /\ Seq.equal (as_seq h1 mac2) mac2_s
    )

val expand_mac3:
    #kcs: supportedKemCipherSuite
    -> prk4e3m: hash_out_buff kcs
    -> ctx3: context3 kcs
    -> mac3: mac23_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_context3 h0 ctx3 /\ live h0 prk4e3m /\ live h0 mac3
        /\ B.all_disjoint [loc prk4e3m; context3_union ctx3; loc mac3]
    )
    (ensures fun h0 _ h1 ->
        let mac3_s = Spec.expand_mac3 #kcs (as_seq h0 prk4e3m) (context3_eval h0 ctx3) in

        modifies1 mac3 h0 h1
        /\ Seq.equal (as_seq h1 mac3) mac3_s
    )