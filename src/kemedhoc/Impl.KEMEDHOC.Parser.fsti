module Impl.KEMEDHOC.Parser

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

open Impl.KEMEDHOC.Types

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

open Spec.KEMEDHOC.Base.Definitions
module Spec = Spec.KEMEDHOC.Parser
module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecSerdEdhoc = Spec.EDHOC.Serialization

open LowStar.BufferOps

open Impl.KEMEDHOC.CryptoPrimitives

(*---------------------------- Utility sizes*)
inline_for_extraction
let plaintext1_size_t = size Spec.id_cred_size +! size Spec.cred_size
inline_for_extraction
let plaintext2_size_t (kcs: supportedKemCipherSuite)
    = size Spec.c_id_size +! size Spec.id_cred_size +! size Spec.cred_size +! size (SpecCrypto.mac23_size kcs)
inline_for_extraction
let plaintext3_size_t (kcs: supportedKemCipherSuite)
    = size Spec.id_cred_size +! size (SpecCrypto.mac23_size kcs)

(*---------------------------- Utility buffers*)
inline_for_extraction
type c_id_buffer = lbuffer uint8 (size Spec.c_id_size)
inline_for_extraction
type id_cred_buffer = lbuffer uint8 (size Spec.id_cred_size)
inline_for_extraction
type cred_buffer = lbuffer uint8 (size Spec.cred_size)

(*---------------------------- Plaintext 1*)
unopteq type plaintext1 = {
    id_cred_I: id_cred_buffer;
    cred_I: cred_buffer
}

let plaintext1_disjoint (p1: plaintext1)
    = disjoint p1.id_cred_I p1.cred_I

let plaintext1_live (h: HS.mem) (p1: plaintext1) 
    = live h p1.id_cred_I /\ live h p1.cred_I

let is_valid_plaintext1 (h: HS.mem) (p1: plaintext1)
    = plaintext1_disjoint p1 /\ plaintext1_live h p1

let plaintext1_union (p1: plaintext1)
    = loc p1.id_cred_I |+| loc p1.cred_I

let plaintext1_modifies (p1: plaintext1) (h0 h1: HS.mem)
    = modifies (plaintext1_union p1) h0 h1

let lemma_plaintext1_union_disjoint (#len: size_t) (h: HS.mem) (p1: plaintext1) (b: lbuffer uint8 len)
    : Lemma (requires is_valid_plaintext1 h p1)
    (ensures B.loc_disjoint (loc b) (plaintext1_union p1) <==> B.all_disjoint [loc b; loc p1.id_cred_I; loc p1.cred_I])
    = ()

// convert the low-level plaintext1 to the high-level sequence
let plaintext1_eval (h: HS.mem) (p1: plaintext1)
    : GTot (Spec.plaintext1)
    = {
        id_cred_I = as_seq h p1.id_cred_I;
        cred_I = as_seq h p1.cred_I
    }

(*---------------------------- Message 1 Type*)
unopteq type message1 (kcs: supportedKemCipherSuite) = {
    method: lbuffer uint8 1ul; // 1 byte
    suite_i: lbuffer uint8 1ul; // 1 byte
    pk_x: kem_pub_key_buff kcs;
    ct_auth_R: kem_ciphertext_buff kcs;
    c_i: c_id_buffer;
    c1: c1_buff kcs;
    // does not support EAD1
}

let message1_disjoint (#kcs: supportedKemCipherSuite) (m1: message1 kcs)
    = B.all_disjoint [loc m1.method; loc m1.suite_i; loc m1.pk_x; loc m1.ct_auth_R; loc m1.c_i; loc m1.c1]

let message1_live (#kcs: supportedKemCipherSuite) (h: HS.mem) (m1: message1 kcs)
    = live h m1.method /\ live h m1.suite_i /\live h m1.pk_x
    /\ live h m1.ct_auth_R /\ live h m1.c_i /\ live h m1.c1

let is_legit_message1 (#kcs: supportedKemCipherSuite) (h: HS.mem) (m1: message1 kcs) 
    = (SpecSerdEdhoc.bytes_to_nat (as_seq h m1.method) = 5)
      /\ (SpecSerdEdhoc.bytes_to_nat (as_seq h m1.suite_i) = 9)

let is_valid_message1 (#kcs: supportedKemCipherSuite) (h: HS.mem) (m1: message1 kcs) 
    = message1_disjoint m1 /\ message1_live h m1
    /\ is_legit_message1 h m1
      

type legitMessage1 (kcs: supportedKemCipherSuite) (h: HS.mem) = m1:message1 kcs{is_legit_message1 h m1} 

// convert the low-level message1 to the high-level sequence
let message1_eval (#kcs: supportedKemCipherSuite) (h: HS.mem) (m1: legitMessage1 kcs h) 
    : GTot (Spec.message1 #kcs)
    = let method_nat = SpecSerdEdhoc.bytes_to_nat (as_seq h m1.method) in
    let suite_label = SpecSerdEdhoc.bytes_to_nat (as_seq h m1.suite_i) in
    {
        method = nat_to_method method_nat;
        suite_i = suite_label;
        pk_x = as_seq h m1.pk_x;
        ct_auth_R = as_seq h m1.ct_auth_R;
        c_i = as_seq h m1.c_i;
        c1 = as_seq h m1.c1
    }

let message1_union (#kcs: supportedKemCipherSuite) (m1: message1 kcs)
    = loc m1.method |+| loc m1.suite_i |+| loc m1.pk_x
    |+| loc m1.ct_auth_R |+| loc m1.c_i |+| loc m1.c1

(*---------------------------- Plaintext 2*)
unopteq type plaintext2 (kcs: supportedKemCipherSuite) = {
    c_R: c_id_buffer;
    id_cred_R: id_cred_buffer;
    cred_R: cred_buffer;
    // does not support EAD2
    mac2: mac23_buff kcs;
}

let plaintext2_disjoint (#kcs: supportedKemCipherSuite) (p2: plaintext2 kcs)
    = B.all_disjoint [loc p2.c_R; loc p2.id_cred_R; loc p2.cred_R; loc p2.mac2]

let plaintext2_live (#kcs: supportedKemCipherSuite) (h: HS.mem) (p2: plaintext2 kcs)
    = live h p2.c_R /\ live h p2.id_cred_R /\ live h p2.cred_R /\ live h p2.mac2

let is_valid_plaintext2 (#kcs: supportedKemCipherSuite) (h: HS.mem) (p2: plaintext2 kcs)
    = plaintext2_disjoint p2 /\ plaintext2_live h p2

let plaintext2_union (#kcs: supportedKemCipherSuite) (p2: plaintext2 kcs)
    = loc p2.c_R |+| loc p2.id_cred_R |+| loc p2.cred_R |+| loc p2.mac2

// convert the low-level plaintext2 to the high-level sequence
let plaintext2_eval (#kcs: supportedKemCipherSuite) (h: HS.mem) (p2: plaintext2 kcs)
    : GTot (Spec.plaintext2 #kcs)
    = {
        c_R = as_seq h p2.c_R;
        id_cred_R = as_seq h p2.id_cred_R;
        cred_R = as_seq h p2.cred_R;
        mac2 = as_seq h p2.mac2
    }

let plaintext2_modifies (#kcs: supportedKemCipherSuite) (p2: plaintext2 kcs) (h0 h1: HS.mem)
    = modifies (plaintext2_union p2) h0 h1

(*---------------------------- Message 2 Type*)
unopteq type message2 (kcs: supportedKemCipherSuite) = {
    ct_y: kem_ciphertext_buff kcs;
    ct_auth_I: kem_ciphertext_buff kcs;
    c2: c2_buff kcs;
    // does not support EAD2
}

let message2_disjoint (#kcs: supportedKemCipherSuite) (m2: message2 kcs)
    = B.all_disjoint [loc m2.ct_y; loc m2.ct_auth_I; loc m2.c2]

let message2_live (#kcs: supportedKemCipherSuite) (h: HS.mem) (m2: message2 kcs)
    = live h m2.ct_y /\ live h m2.ct_auth_I /\ live h m2.c2

let is_valid_message2 (#kcs: supportedKemCipherSuite) (h: HS.mem) (m2: message2 kcs)
    = message2_disjoint m2 /\ message2_live h m2

let message2_union (#kcs: supportedKemCipherSuite) (m2: message2 kcs)
    = loc m2.ct_y |+| loc m2.ct_auth_I |+| loc m2.c2

// convert the low-level message2 to the high-level sequence
let message2_eval (#kcs: supportedKemCipherSuite) (h: HS.mem) (m2: message2 kcs)
    : GTot (Spec.message2 #kcs)
    = {
        ct_y = as_seq h m2.ct_y;
        ct_auth_I = as_seq h m2.ct_auth_I;
        c2 = as_seq h m2.c2
    }

(*---------------------------- Plaintext 3*)
unopteq type plaintext3 (kcs: supportedKemCipherSuite) = {
    id_cred_I: id_cred_buffer;
    // does not support EAD3
    mac3: mac23_buff kcs
}

let plaintext3_disjoint (#kcs: supportedKemCipherSuite) (p3: plaintext3 kcs)
    = disjoint p3.id_cred_I p3.mac3

let plaintext3_live (#kcs: supportedKemCipherSuite) (h: HS.mem) (p3: plaintext3 kcs)
    = live h p3.id_cred_I /\ live h p3.mac3

let is_valid_plaintext3 (#kcs: supportedKemCipherSuite) (h: HS.mem) (p3: plaintext3 kcs)
    = plaintext3_disjoint p3 /\ plaintext3_live h p3

let plaintext3_union (#kcs: supportedKemCipherSuite) (p3: plaintext3 kcs)
    = loc p3.id_cred_I |+| loc p3.mac3

// convert the low-level plaintext3 to the high-level sequence
let plaintext3_eval (#kcs: supportedKemCipherSuite) (h: HS.mem) (p3: plaintext3 kcs)
    : GTot (Spec.plaintext3 #kcs)
    = {
        id_cred_I = as_seq h p3.id_cred_I;
        mac3 = as_seq h p3.mac3
    }

let plaintext3_modifies (#kcs: supportedKemCipherSuite) (p3: plaintext3 kcs) (h0 h1: HS.mem)
    = modifies (plaintext3_union p3) h0 h1

(*---------------------------- Message 3 Type*)
type message3 (kcs: supportedKemCipherSuite) = lbuffer uint8 (size (Spec.c3_size kcs))

(*--------------------------------------*)
(*---------------------------- Parsing*)
(*--------------------------------------*)

/// ------------------------
/// Plaintext 1
/// ------------------------
let construct_plaintext1 (id_cred_I: id_cred_buffer)
    (cred_I: cred_buffer)
    : Tot plaintext1
    = { id_cred_I = id_cred_I; cred_I = cred_I }

val concat_ptx1:
    p1: plaintext1
    -> p1_buffer: plaintext1_buff
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_plaintext1 h0 p1
        /\ live h0 p1_buffer
        /\ B.loc_disjoint (loc p1_buffer) (plaintext1_union p1)
    )
    (ensures fun h0 _ h1 ->
        let p1_s = plaintext1_eval h0 p1 in
        let p1_s_concat = Spec.concat_ptx1 p1_s in

        modifies1 p1_buffer h0 h1
        /\ Seq.equal (as_seq h1 p1_buffer) p1_s_concat
    )

val deserialize_ptx1:
    p1_buffer: plaintext1_buff
    -> p1: plaintext1
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 p1_buffer /\ is_valid_plaintext1 h0 p1
        /\ B.loc_disjoint (loc p1_buffer) (plaintext1_union p1)
    )
    (ensures fun h0 _ h1 ->
        let p1_s_deserd = plaintext1_eval h1 p1 in
        let p1_s = Spec.deserialize_ptx1 (as_seq h0 p1_buffer) in

        plaintext1_modifies p1 h0 h1
        /\ Seq.equal p1_s_deserd.id_cred_I p1_s.id_cred_I
        /\ Seq.equal p1_s_deserd.cred_I p1_s.cred_I
    )

/// ------------------------
/// Message 1
/// ------------------------
let construct_message1 (kcs: supportedKemCipherSuite)
    (method: lbuffer uint8 1ul) (suite_i: lbuffer uint8 1ul)
    (pk_x: kem_pub_key_buff kcs) (ct_auth_R: kem_ciphertext_buff kcs)
    (c_i: c_id_buffer) (c1: c1_buff kcs)
    : Tot (message1 kcs)
    = { method = method; suite_i = suite_i; pk_x = pk_x; ct_auth_R = ct_auth_R; c_i = c_i; c1 = c1 }

let concat_msg1_fixed_length_t (kcs: supportedKemCipherSuite)
    = size (Spec.concat_msg1_fixed_length kcs)

val concat_msg1:
    kcs: supportedKemCipherSuite
    -> msg1: message1 kcs
    -> msg1_buffer: lbuffer uint8 (concat_msg1_fixed_length_t kcs)
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_message1 h0 msg1 /\ live h0 msg1_buffer
        /\ B.loc_disjoint (loc msg1_buffer) (message1_union msg1)
    )
    (ensures fun h0 _ h1 ->
        let m1_s = message1_eval h0 msg1 in
        let m1_s_concat = Spec.concat_msg1 #kcs m1_s in

        modifies1 msg1_buffer h0 h1
        /\ Seq.equal (as_seq h1 msg1_buffer) m1_s_concat
    )

/// ------------------------
/// Plaintext 2
/// ------------------------
let construct_plaintext2 (kcs: supportedKemCipherSuite)
    (c_R: c_id_buffer) (id_cred_R: id_cred_buffer)
    (cred_R: cred_buffer) (mac2: mac23_buff kcs)
    : Tot (plaintext2 kcs)
    = { c_R = c_R; id_cred_R = id_cred_R; cred_R = cred_R; mac2 = mac2 }

val concat_ptx2:
    kcs: supportedKemCipherSuite
    -> p2: plaintext2 kcs
    -> p2_buffer: plaintext2_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_plaintext2 h0 p2 /\ live h0 p2_buffer
        /\ B.loc_disjoint (loc p2_buffer) (plaintext2_union p2)
    )
    (ensures fun h0 _ h1 ->
        let p2_s = plaintext2_eval #kcs h0 p2 in
        let p2_s_concat = Spec.concat_ptx2 #kcs p2_s in

        modifies1 p2_buffer h0 h1
        /\ Seq.equal (as_seq h1 p2_buffer) p2_s_concat
    )

val deserialize_ptx2:
    kcs: supportedKemCipherSuite
    -> p2_buffer: plaintext2_buff kcs
    -> p2: plaintext2 kcs
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_plaintext2 h0 p2 /\ live h0 p2_buffer
        /\ B.loc_disjoint (loc p2_buffer) (plaintext2_union p2)
    )
    (ensures fun h0 _ h1 ->
        let p2_s_deserd = plaintext2_eval h1 p2 in
        let p2_s = Spec.deserialize_ptx2 (as_seq h0 p2_buffer) in

        plaintext2_modifies p2 h0 h1
        /\ Seq.equal p2_s_deserd.c_R p2_s.c_R
        /\ Seq.equal p2_s_deserd.id_cred_R p2_s.id_cred_R
        /\ Seq.equal p2_s_deserd.cred_R p2_s.cred_R
        /\ Seq.equal p2_s_deserd.mac2 p2_s.mac2
    )

/// ------------------------
/// Message 2
/// ------------------------
let construct_msg2 (kcs: supportedKemCipherSuite)
    (ct_y: kem_ciphertext_buff kcs) (ct_auth_I: kem_ciphertext_buff kcs)
    (c2: c2_buff kcs)
    : Tot (message2 kcs)
    = { ct_y = ct_y; ct_auth_I = ct_auth_I; c2 = c2 }

let concat_msg2_get_fixed_length (kcs: supportedKemCipherSuite)
    = size (SpecCrypto.kem_ciphertext_size kcs) +! size (SpecCrypto.kem_ciphertext_size kcs)
    +! size (Spec.c2_size kcs)

val concat_msg2:
    kcs: supportedKemCipherSuite
    -> msg2: message2 kcs
    -> msg2_buffer: lbuffer uint8 (concat_msg2_get_fixed_length kcs)
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_message2 h0 msg2 /\ live h0 msg2_buffer
        /\ B.loc_disjoint (loc msg2_buffer) (message2_union msg2)
    )
    (ensures fun h0 _ h1 ->
        let m2_s = message2_eval #kcs h0 msg2 in
        let m2_s_concat = Spec.concat_msg2 #kcs m2_s in

        modifies1 msg2_buffer h0 h1
        /\ Seq.equal (as_seq h1 msg2_buffer) m2_s_concat
    )

/// ------------------------
/// Plaintext 3
/// ------------------------
let construct_msg3 (kcs: supportedKemCipherSuite)
    (id_cred_I: id_cred_buffer) (mac3: mac23_buff kcs)
    : Tot (plaintext3 kcs)
    = { id_cred_I = id_cred_I; mac3 = mac3 }

val concat_ptx3:
    kcs: supportedKemCipherSuite
    -> p3: plaintext3 kcs
    -> p3_buffer: plaintext3_buff kcs
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_plaintext3 h0 p3 /\ live h0 p3_buffer
        /\ B.loc_disjoint (loc p3_buffer) (plaintext3_union p3)
    )
    (ensures fun h0 _ h1 ->
        let p3_s = plaintext3_eval #kcs h0 p3 in
        let p3_s_concat = Spec.concat_ptx3 #kcs p3_s in

        modifies1 p3_buffer h0 h1
        /\ Seq.equal (as_seq h1 p3_buffer) p3_s_concat
    )

val deserialize_ptx3:
    kcs: supportedKemCipherSuite
    -> p3_buffer: plaintext3_buff kcs
    -> p3: plaintext3 kcs
    -> ST.Stack unit
    (requires fun h0 ->
        is_valid_plaintext3 h0 p3 /\ live h0 p3_buffer
        /\ B.loc_disjoint (loc p3_buffer) (plaintext3_union p3)
    )
    (ensures fun h0 _ h1 ->
        let p3_s_deserd = plaintext3_eval h1 p3 in
        let p3_s = Spec.deserialize_ptx3 #kcs (as_seq h0 p3_buffer) in

        plaintext3_modifies p3 h0 h1
        /\ Seq.equal (as_seq h1 p3.id_cred_I) p3_s.id_cred_I
        /\ Seq.equal p3_s_deserd.mac3 p3_s.mac3
    )