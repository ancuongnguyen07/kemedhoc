module Impl.KEMEDHOC.Parser

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

module Spec = Spec.KEMEDHOC.Parser
friend Spec.KEMEDHOC.Parser

module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives

open Impl.EDHOC.Utilities

(*--------------------------------------*)
(*---------------------------- Parsing*)
(*--------------------------------------*)

/// ------------------------
/// Plaintext 1
/// ------------------------
let concat_ptx1 p1 p1_buffer
    = concat_buff2 p1.id_cred_I p1.cred_I p1_buffer

let deserialize_ptx1 p1_buffer p1
    = (**) let h0 = ST.get () in
    let id_cred_I_buffer = sub p1_buffer 0ul (size Spec.id_cred_size) in
    copy p1.id_cred_I id_cred_I_buffer;
    (**) let h1 = ST.get () in
    (**) assert(modifies1 (p1.id_cred_I) h0 h1);
    
    let cred_I_buffer = sub p1_buffer (size Spec.id_cred_size) (size Spec.cred_size) in
    copy p1.cred_I cred_I_buffer;
    (**) let h2 = ST.get () in
    assert(modifies2 p1.id_cred_I p1.cred_I h0 h2);
    ()

/// ------------------------
/// Message 1
/// ------------------------
let concat_msg1 kcs msg1 msg1_buffer
    = concat_buff6 msg1.method msg1.suite_i msg1.pk_x msg1.ct_auth_R msg1.c_i msg1.c1 msg1_buffer

/// ------------------------
/// Plaintext 2
/// ------------------------
let concat_ptx2 kcs p2 p2_buffer
    = concat_buff4 p2.c_R p2.id_cred_R p2.cred_R p2.mac2 p2_buffer

let deserialize_ptx2 kcs p2_buffer p2
    = (**) let h0 = ST.get () in
    let c_R_buffer = sub p2_buffer 0ul (size Spec.c_id_size) in
    copy p2.c_R c_R_buffer;
    (**) let h1 = ST.get () in
    (**) assert(modifies1 (p2.c_R) h0 h1);
    
    let id_cred_R_buffer = sub p2_buffer (size Spec.c_id_size) (size Spec.id_cred_size) in
    copy p2.id_cred_R id_cred_R_buffer;
    (**) let h2 = ST.get () in
    assert(modifies2 p2.c_R p2.id_cred_R h0 h2);
    
    let cred_R_buffer = sub p2_buffer (size Spec.c_id_size +! size Spec.id_cred_size) (size Spec.cred_size) in
    copy p2.cred_R cred_R_buffer;
    (**) let h3 = ST.get () in
    assert(modifies3 p2.c_R p2.id_cred_R p2.cred_R h0 h3);
    
    let mac2_buffer = sub p2_buffer (size Spec.c_id_size +! size Spec.id_cred_size +! size Spec.cred_size) (size (SpecCrypto.mac23_size kcs)) in
    copy p2.mac2 mac2_buffer;
    (**) let h4 = ST.get () in
    assert(modifies4 p2.c_R p2.id_cred_R p2.cred_R p2.mac2 h0 h4);
    ()

/// ------------------------
/// Message 2
/// ------------------------
let concat_msg2 kcs msg2 msg2_buffer
    = concat_buff3 msg2.ct_y msg2.ct_auth_I msg2.c2 msg2_buffer

/// ------------------------
/// Plaintext 3
/// ------------------------
let concat_ptx3 kcs p3 p3_buffer
    = concat_buff2 p3.id_cred_I p3.mac3 p3_buffer

let deserialize_ptx3 kcs p3_buffer p3
    = (**) let h0 = ST.get () in
    let id_cred_I_buffer = sub p3_buffer 0ul (size Spec.id_cred_size) in
    copy p3.id_cred_I id_cred_I_buffer;
    (**) let h1 = ST.get () in
    (**) assert(modifies1 (p3.id_cred_I) h0 h1);
    (**) assert(
        let p3_s = Spec.deserialize_ptx3 #kcs (as_seq h0 p3_buffer) in
        Seq.equal p3_s.id_cred_I (as_seq h1 p3.id_cred_I)
    );

    let mac3_buffer = sub p3_buffer (size Spec.id_cred_size) (size (SpecCrypto.mac23_size kcs)) in
    copy p3.mac3 mac3_buffer;
    (**) let h2 = ST.get () in
    (**) assert(modifies1 p3.mac3 h1 h2);
    (**) assert(modifies2 p3.id_cred_I p3.mac3 h0 h2);
    (**) assert(
        let p3_s = Spec.deserialize_ptx3 #kcs (as_seq h0 p3_buffer) in
        let p3_s_deserd = plaintext3_eval h2 p3 in

        Seq.equal p3_s.mac3 (as_seq h2 p3.mac3)
        /\ Seq.equal p3_s.mac3 p3_s_deserd.mac3
    );
    ()
