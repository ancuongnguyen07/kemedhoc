module Impl.KEMEDHOC.KeySchedule

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence


module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives

module Spec = Spec.KEMEDHOC.KeySchedule
friend Spec.KEMEDHOC.KeySchedule

// open Spec.EDHOC.Serialization

(*---------------------------- HKDF Info*)
let concat_info i context_len okm_len i_buffer
    = concat_buff3 #MUT #uint8 #1ul #context_len #okm_len i.label i.context i.okm_len i_buffer

(*---------------------------- HKDF context*)

/// ---------------
/// Context 2
/// ---------------
let concat_context2 #kcs ctx2 ctx2_buffer
    = concat_buff4 ctx2.c_r ctx2.id_cred_r ctx2.th2 ctx2.cred_r ctx2_buffer

/// ---------------
/// Context 3
/// ---------------
let concat_context3 #kcs ctx3 ctx3_buffer
    = concat_buff3 ctx3.id_cred_i ctx3.th3 ctx3.cred_i ctx3_buffer

(*---------------------------- HKDF key schedule*)

/// ---------------
/// PRK
/// ---------------
let extract_prk1e #kcs th1 k_auth_R prk1e
    = let salt_len = size (SpecCrypto.hash_size kcs) in
    let ikm_len = kem_shared_secret_size_t kcs in
    hkdf_extract kcs prk1e salt_len th1 ikm_len k_auth_R

let extract_prk2e #kcs prk1e th2 k_xy prk2e
    = ST.push_frame();
    (**) let h0 = ST.get () in

    let prk1e_th2_concat_len = size (SpecCrypto.hash_size kcs) +! size (SpecCrypto.hash_size kcs) in
    let prk1e_th2_concat = create prk1e_th2_concat_len (u8 0) in
    concat_buff2 prk1e th2 prk1e_th2_concat;
    (**) let h1 = ST.get () in

    let prk1e_th2_digest_len = size (SpecCrypto.hash_size kcs) in
    let prk1e_th2_digest = create prk1e_th2_digest_len (u8 0) in
    do_hash kcs prk1e_th2_digest prk1e_th2_concat_len prk1e_th2_concat;
    (**) let h2 = ST.get () in

    let salt_len = size (SpecCrypto.hash_size kcs) in
    let ikm_len = kem_shared_secret_size_t kcs in
    hkdf_extract kcs prk2e salt_len prk1e_th2_digest ikm_len k_xy;
    (**) let h3 = ST.get () in

    ST.pop_frame();
    ()

let extract_prk3e2m #kcs salt3e2m k_auth_R prk3e2m
    = let salt_len = size (SpecCrypto.hash_size kcs) in
    let ikm_len = kem_shared_secret_size_t kcs in
    hkdf_extract kcs prk3e2m salt_len salt3e2m ikm_len k_auth_R

let extract_prk4e3m #kcs salt4e3m k_auth_I prk4e3m
    = let salt_len = size (SpecCrypto.hash_size kcs) in
    let ikm_len = kem_shared_secret_size_t kcs in
    hkdf_extract kcs prk4e3m salt_len salt4e3m ikm_len k_auth_I

let expand_prk_out #kcs prk4e3m th4 prk_out
    = ST.push_frame();
    (**) let h0 = ST.get () in
    let hash_size = size (SpecCrypto.hash_size kcs) in
    let okm_len = hash_size in
    let prk_len = hash_size in

    /// Construct HKDF info
    let info_label_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul info_label_buffer Spec.info_label_prk_out;
    let okm_len_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul okm_len_buffer (SpecCrypto.hash_size kcs);
    let context_len = hash_size in
    let context_buffer = th4 in
    // let info = construct_info info_label_buffer context_buffer okm_len_buffer in
    let info_concat_len = 1ul +! context_len +! 1ul in
    let info_concat_buffer = create info_concat_len (u8 0) in
    // concat_info info context_len 1ul info_concat_buffer;
    concat_buff3 info_label_buffer context_buffer okm_len_buffer info_concat_buffer;
    (**) let h1 = ST.get () in

    hkdf_expand kcs okm_len prk_out prk_len prk4e3m info_concat_len info_concat_buffer;
    (**) let h2 = ST.get () in
    (**) assert(
        let info_struct = Spec.construct_info Spec.info_label_prk_out (as_seq h0 th4) (SpecCrypto.hash_size kcs) in
        let info_byte = Spec.concat_info info_struct in

        Seq.equal (as_seq h1 info_concat_buffer) info_byte
    );

    ST.pop_frame();
    ()

let expand_prk_exporter #kcs prk_out prk_exporter
    = ST.push_frame();
    (**) let h0 = ST.get () in
    let hash_size = size (SpecCrypto.hash_size kcs) in
    let okm_len = hash_size in
    let prk_len = hash_size in

    // construct HKDF info with an empty context
    let info_label_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul info_label_buffer Spec.info_label_prk_exporter;
    let okm_len_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul okm_len_buffer (SpecCrypto.hash_size kcs);
    let info_concat_len = 1ul +! 1ul in
    let info_concat_buffer = create info_concat_len (u8 0) in
    concat_buff2 info_label_buffer okm_len_buffer info_concat_buffer;
    (**) let h1 = ST.get () in

    hkdf_expand kcs okm_len prk_exporter prk_len prk_out info_concat_len info_concat_buffer; 

    ST.pop_frame();
    ()

/// ---------------
/// Encryption Key
/// ---------------
let expand_k #kcs key_label prk th k
    = ST.push_frame();
    (**) let h0 = ST.get () in
    let hash_size = size (SpecCrypto.hash_size kcs) in
    let okm_len = SpecCrypto.aead_key_size kcs in

    // construct HKDF info
    let info_label_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul info_label_buffer key_label;
    let okm_len_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul okm_len_buffer okm_len;
    let context_buffer = th in
    let info_concat_len = 1ul +! hash_size +! 1ul in
    let info_concat_buffer = create info_concat_len (u8 0) in
    concat_buff3 info_label_buffer context_buffer okm_len_buffer info_concat_buffer;
    (**) let h1 = ST.get () in

    hkdf_expand kcs (size okm_len) k hash_size prk info_concat_len info_concat_buffer;
    (**) let h2 = ST.get () in
    (**) assert(
        let info_struct = Spec.construct_info key_label (as_seq h0 th) okm_len in
        let info_byte = Spec.concat_info info_struct in

        Seq.equal (as_seq h1 info_concat_buffer) info_byte
    );

    ST.pop_frame();
    ()

/// ---------------
/// Initial Vector
/// ---------------
let expand_iv #kcs iv_label prk th iv
    = ST.push_frame();
    (**) let h0 = ST.get () in
    let hash_size = size (SpecCrypto.hash_size kcs) in

    // construct HKDF info
    let info_label_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul info_label_buffer iv_label;
    let okm_len = SpecCrypto.aead_iv_size in
    let okm_len_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul okm_len_buffer okm_len;
    let context_buffer = th in
    let info_concat_len = 1ul +! hash_size +! 1ul in
    let info_concat_buffer = create info_concat_len (u8 0) in
    concat_buff3 info_label_buffer context_buffer okm_len_buffer info_concat_buffer;
    (**) let h1 = ST.get () in

    hkdf_expand kcs (size okm_len) iv hash_size prk info_concat_len info_concat_buffer;
    (**) let h2 = ST.get () in
    (**) assert(
        let info_struct = Spec.construct_info iv_label (as_seq h0 th) okm_len in
        let info_byte = Spec.concat_info info_struct in

        Seq.equal (as_seq h1 info_concat_buffer) info_byte
    );

    ST.pop_frame();
    ()

/// ---------------
/// SALT
/// ---------------
let expand_salt #kcs salt_label prk th salt
    = ST.push_frame();
    (**) let h0 = ST.get () in
    let hash_size = (SpecCrypto.hash_size kcs) in

    // construct HKDF info
    let info_label_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul info_label_buffer salt_label;
    let okm_len = hash_size in
    let okm_len_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul okm_len_buffer okm_len;
    let context_buffer = th in
    let info_concat_len = 1ul +! (size hash_size) +! 1ul in
    let info_concat_buffer = create info_concat_len (u8 0) in
    concat_buff3 info_label_buffer context_buffer okm_len_buffer info_concat_buffer;
    (**) let h1 = ST.get () in

    hkdf_expand kcs (size okm_len) salt (size hash_size) prk info_concat_len info_concat_buffer;
    (**) let h2 = ST.get () in
    (**) assert(
        let info_struct = Spec.construct_info salt_label (as_seq h0 th) okm_len in
        let info_byte = Spec.concat_info info_struct in

        Seq.equal (as_seq h1 info_concat_buffer) info_byte
    );

    ST.pop_frame();
    ()

/// ---------------
/// MAC
/// ---------------
#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
let expand_mac2 #kcs prk3e2m ctx2 mac2
    = ST.push_frame();
    (**) let h0 = ST.get () in
    let hash_size = SpecCrypto.hash_size kcs in

    // concat context2
    let ctx2_concat_len = concat_context2_get_fixed_length kcs in
    let ctx2_concat_buffer = create ctx2_concat_len (u8 0) in
    concat_context2 #kcs ctx2 ctx2_concat_buffer;
    (**) let h1 = ST.get () in
    (**) assert(
        let ctx2_seq = Spec.concat_context2 #kcs (context2_eval h0 ctx2) in

        modifies1 ctx2_concat_buffer h0 h1
        /\  Seq.equal (as_seq h1 ctx2_concat_buffer) ctx2_seq

    );

    // construct HKDF info
    let info_label_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul info_label_buffer Spec.info_label_mac2;
    let okm_len = SpecCrypto.mac23_size kcs in
    let okm_len_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul okm_len_buffer okm_len;
    let info_concat_len = 1ul +! ctx2_concat_len +! 1ul in
    let info_concat_buffer = create info_concat_len (u8 0) in
    concat_buff3 info_label_buffer ctx2_concat_buffer okm_len_buffer info_concat_buffer;
    (**) let h2 = ST.get () in
    (**) assert(
        let ctx2_seq = Spec.concat_context2 #kcs (context2_eval h0 ctx2) in
        let info_struct = Spec.construct_info Spec.info_label_mac2 ctx2_seq okm_len in
        let info_byte = Spec.concat_info info_struct in

        Seq.equal (as_seq h2 info_concat_buffer) info_byte
    );

    hkdf_expand kcs (size okm_len) mac2 (size hash_size) prk3e2m info_concat_len info_concat_buffer;
    (**) let h3 = ST.get () in
    (**) assert(
        modifies1 mac2 h2 h3
    );

    ST.pop_frame();
    ()

let expand_mac3 #kcs prk4e3m ctx3 mac3
    = ST.push_frame();
    (**) let h0 = ST.get () in
    let hash_size = SpecCrypto.hash_size kcs in

    // concat context3
    let ctx3_concat_len = concat_context3_get_fixed_length kcs in
    let ctx3_concat_buffer = create ctx3_concat_len (u8 0) in
    concat_context3 #kcs ctx3 ctx3_concat_buffer;
    (**) let h1 = ST.get () in
    (**) assert(
        let ctx3_seq = Spec.concat_context3 #kcs (context3_eval h0 ctx3) in

        modifies1 ctx3_concat_buffer h0 h1
        /\  Seq.equal (as_seq h1 ctx3_concat_buffer) ctx3_seq

    );

    // construct HKDF info
    let info_label_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul info_label_buffer Spec.info_label_mac3;
    let okm_len = SpecCrypto.mac23_size kcs in
    let okm_len_buffer = create 1ul (u8 0) in
    nat_to_bytes 1ul okm_len_buffer okm_len;
    let info_concat_len = 1ul +! ctx3_concat_len +! 1ul in
    let info_concat_buffer = create info_concat_len (u8 0) in
    concat_buff3 info_label_buffer ctx3_concat_buffer okm_len_buffer info_concat_buffer;
    (**) let h2 = ST.get () in
    (**) assert(
        let ctx3_seq = Spec.concat_context3 #kcs (context3_eval h0 ctx3) in
        let info_struct = Spec.construct_info Spec.info_label_mac3 ctx3_seq okm_len in
        let info_byte = Spec.concat_info info_struct in

        Seq.equal (as_seq h2 info_concat_buffer) info_byte
    );

    hkdf_expand kcs (size okm_len) mac3 (size hash_size) prk4e3m info_concat_len info_concat_buffer;
    (**) let h3 = ST.get () in
    (**) assert(
        modifies1 mac3 h2 h3
    );

    ST.pop_frame();
    ()

#pop-options
