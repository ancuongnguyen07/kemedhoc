module Impl.EDHOC.CryptoPrimitives

(*The corresponding FStar high-level Spec*)
module Spec = Spec.EDHOC.CryptoPrimitives

open FStar.Mul

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
// this module use OCaml crypto-kit.
// Remember to link with OCaml APIs when compile to C.
// look at `hacl-star/lib/ml/Lib_randomBuffer_System_gen.ml`
// open Lib.RandomSequence
open Lib.RandomBuffer.System
// open Lib.RandomSequence
module HACLRandom = Lib.RandomSequence

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

open LowStar.BufferOps

module U32 = FStar.UInt32
module U64 = FStar.UInt64

(*AEAD*)
module SpecAEAD = Spec.Agile.AEAD
module ImplAEAD = EverCrypt.AEAD
module EverCryptError = EverCrypt.Error

(*Hash*)
module SpecHash = Spec.Agile.Hash
module DefHash = Spec.Hash.Definitions

(*HMAC*)
module SpecHMAC = Spec.Agile.HMAC

(*HKDF*)
module SpecHKDF = Spec.Agile.HKDF
module ImplHKDF = Hacl.HKDF

(*DH and Signature related modules*)
module SpecDH = Spec.Agile.DH
module ImplP256 = Hacl.P256
module ImplEDSA25519 = Hacl.Ed25519
module ImplCurve25519_51 = Hacl.Curve25519_51

open TypeHelper.EDHOC

(*----------------------------------------------------*)

(*------------------ DH*)
val secret_to_public:
    #cs:Spec.supported_cipherSuite
    -> priv:ec_priv_key_buf cs
    -> pub:ec_pub_key_buf cs
    -> ST.Stack bool
    (requires fun h0 -> 
        live h0 pub /\ live h0 priv /\ disjoint pub priv
    )
    (ensures fun h0 r h1 -> modifies1 pub h0 h1
        /\ (
            let pk = (Spec.secret_to_public #cs (as_seq h0 priv)) in
            (r <==> Some? pk)
            /\ (r ==> (as_seq h1 pub == Some?.v pk))
        )
    )

val dh:
    #cs:Spec.supported_cipherSuite
    -> output:ec_pub_key_buf cs
    -> priv:ec_priv_key_buf cs
    -> pub:ec_pub_key_buf cs
    -> ST.Stack bool
    (requires fun h0 ->
        live h0 output /\ live h0 priv /\ live h0 pub
        /\ B.all_disjoint [loc pub; loc priv; loc output]
    )
    (ensures fun h0 res h1 -> modifies1 output h0 h1
        /\ (
            let shared_dh = Spec.dh #cs (as_seq h0 priv) (as_seq h0 pub) in
            (res <==> Some? shared_dh)
            /\ (res ==> (as_seq h1 output) == Some?.v shared_dh)
        )
    )

/// ----------------- AEAD Encryption
noextract
let aead_config_pre (cs:Spec.supported_cipherSuite) = ImplAEAD.config_pre (Spec.get_aead_alg cs) 

/// To be compliant to the HACL's Spec, `ctxt` buffer will contains both ciphertext
/// and tag. Note that Vale returns ciphertext and tag separately while HACL
/// bundle them together.
inline_for_extraction noextract
type aead_encrypt_st (a:Spec.aeadAlg) (pre:Type0)
    = key:aead_key_lbuffer a
    -> iv_len:size_t{iv_len = size Spec.aead_iv_size}
    -> iv:lbuffer uint8 iv_len
    -> ad_len:size_t{size_v ad_len <= (Spec.alg_aead_max_input_size a)}
    -> ad:lbuffer uint8 ad_len
    -> ptx_len:size_t{size_v ptx_len <= (Spec.alg_aead_max_input_size a)
                    /\ size_v ptx_len + (Spec.aead_tag_size a) <= max_size_t}
    -> ptx:lbuffer uint8 ptx_len
    -> ctxt:lbuffer uint8 (size (size_v ptx_len + (Spec.aead_tag_size a)))
    -> ST.Stack c_response
    (requires fun h0 ->
        // pre /\ 
        live h0 key /\ live h0 iv /\ live h0 ad /\ live h0 ptx /\ live h0 ctxt
        /\ B.all_disjoint [loc key; loc iv; loc ad; loc ptx; loc ctxt]
    )
    (ensures fun h0 res h1 -> 
        (
            match res with
                | CSuccess -> modifies1 ctxt h0 h1 /\
                    as_seq h1 ctxt
                        == Spec.alg_aead_encrypt a (as_seq h0 key) (as_seq h0 iv) (as_seq h0 ad) (as_seq h0 ptx)
                | CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
                | _ -> False
        )
    )

inline_for_extraction
val aead_aes256_gcm_encrypt:aead_encrypt_st SpecAEAD.AES256_GCM (ImplAEAD.config_pre SpecAEAD.AES256_GCM)

inline_for_extraction
val aead_aes128_gcm_encrypt:aead_encrypt_st SpecAEAD.AES128_GCM (ImplAEAD.config_pre SpecAEAD.AES128_GCM)

let aead_encrypt (cs:Spec.supported_cipherSuite)
    : aead_encrypt_st (Spec.get_aead_alg cs) (aead_config_pre cs)
    = match (Spec.get_aead_alg cs) with
        | SpecAEAD.AES128_GCM -> aead_aes128_gcm_encrypt
        | SpecAEAD.AES256_GCM -> aead_aes256_gcm_encrypt

/// ----------------- AEAD Decryption

// To be compliant to the Spec, `ctxt` buffer will contains both ciphertext
// and tag. Note that Vale returns ciphertext and tag separately while HACL
// bundle them together.
type aead_decrypt_st (a:Spec.aeadAlg) (pre:Type0)
    = key:aead_key_lbuffer a
    -> iv_len:size_t{iv_len = size Spec.aead_iv_size}
    -> iv:lbuffer uint8 iv_len
    -> ad_len:size_t{size_v ad_len <= (Spec.alg_aead_max_input_size a)}
    -> ad:lbuffer uint8 ad_len
    -> ptx_len:size_t{size_v ptx_len + (Spec.aead_tag_size a) <= max_size_t}
    -> ptx:lbuffer uint8 ptx_len
    -> ctxt:lbuffer uint8 (size (size_v ptx_len + (Spec.aead_tag_size a)))
    -> ST.Stack c_response
    (requires fun h0 ->
        // pre /\
        live h0 key /\ live h0 iv /\ live h0 ad /\ live h0 ptx /\ live h0 ctxt
        /\ B.all_disjoint [loc key; loc iv; loc ad; loc ptx; loc ctxt]
    )
    (ensures fun h0 res h1 ->
        let res_abstract
            = (Spec.alg_aead_decrypt a (as_seq h0 key) (as_seq h0 iv) (as_seq h0 ad) (as_seq h0 ctxt)) in
        (
            match (res, res_abstract) with
                | CDecryptionFailure, None -> modifies1 ptx h0 h1
                | CUnsupportedAlgorithmOrInvalidConfig, _ -> modifies0 h0 h1
                | CSuccess, Some plaintext -> modifies1 ptx h0 h1 /\ plaintext == as_seq h1 ptx
                | _ -> False
        )
    )

inline_for_extraction
val aead_aes256_gcm_decrypt:aead_decrypt_st SpecAEAD.AES256_GCM (ImplAEAD.config_pre SpecAEAD.AES256_GCM)

inline_for_extraction
val aead_aes128_gcm_decrypt:aead_decrypt_st SpecAEAD.AES128_GCM (ImplAEAD.config_pre SpecAEAD.AES128_GCM)

let aead_decrypt (cs:Spec.supported_cipherSuite)
    = match (Spec.get_aead_alg cs) with
        | SpecAEAD.AES128_GCM -> aead_aes128_gcm_decrypt
        | SpecAEAD.AES256_GCM -> aead_aes256_gcm_decrypt

(*-------------------- Hash*)
inline_for_extraction noextract
type do_hash_st (a:Spec.hashAlg) (precondition:Type0)
    = output:alg_hash_out_buff a
    -> input_len:size_t{size_v input_len <= (Spec.alg_get_hash_max_input a)}
    -> input:lbuffer uint8 input_len
    -> ST.Stack unit
    (requires fun h0 ->
        precondition /\ live h0 output /\ live h0 input
        /\ disjoint output input
    )
    (ensures fun h0 _ h1 -> modifies1 output h0 h1
        /\ as_seq h1 output == Spec.alg_do_hash a (as_seq h0 input)            
    )

inline_for_extraction noextract
val hash_sha2_256:do_hash_st SpecHash.SHA2_256 True

inline_for_extraction noextract
let hash_pre (cs:Spec.supported_cipherSuite):Type0
    = match (Spec.get_hash_alg cs) with
        | SpecHash.SHA2_256 -> True

inline_for_extraction
let do_hash (cs:Spec.supported_cipherSuite):do_hash_st (Spec.get_hash_alg cs) (hash_pre cs)
    = match (Spec.get_hash_alg cs) with
        | SpecHash.SHA2_256 -> hash_sha2_256

(*-------------------- HMAC*)
inline_for_extraction noextract
type hmac_st (a:Spec.hashAlg)
    = output:alg_hash_out_buff a
    -> key_len:size_t{size_v key_len + SpecHash.block_length a < pow2 32}
    -> key:lbuffer uint8 key_len
    -> data_len:size_t{size_v data_len + SpecHash.block_length a < pow2 32}
    -> data:lbuffer uint8 data_len
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 key /\ live h0 data /\ live h0 output
        /\ B.all_disjoint [loc output; loc key; loc data]
    )
    (ensures fun h0 _ h1 -> modifies1 output h0 h1
        /\ as_seq h1 output == Spec.alg_hmac a (as_seq h0 key) (as_seq h0 data)
    )

inline_for_extraction noextract
val hmac_sha2_256:hmac_st SpecHash.SHA2_256

inline_for_extraction
let hmac (cs:Spec.supported_cipherSuite):hmac_st (Spec.get_hash_alg cs)
    = match (Spec.get_hash_alg cs) with
        | SpecHash.SHA2_256 -> hmac_sha2_256

(*-------------------- HKDF*)
/// ----------------- HKDF Expand
inline_for_extraction noextract
type hkdf_expand_st (a:Spec.hashAlg)
    = okm_len:size_t{SpecHKDF.expand_output_length_pred a (size_v okm_len)}
    -> okm:lbuffer uint8 okm_len
    -> prk_len:size_t{size_v prk_len = Spec.alg_hash_size a}
    -> prk:lbuffer uint8 prk_len
    // Note that the requirement of `info_len` below is DIFFERENT from
    // the HACL's Spec. There are many inconsistencies between
    // preconditions of HACL spec and HACL impl.
    -> info_len:size_t{Spec.alg_hash_size a + size_v info_len + 1 + DefHash.block_length a < pow2 32}
    -> info:lbuffer uint8 info_len
    -> ST.Stack unit
    (requires fun h0 ->
        SpecHMAC.keysized a (size_v prk_len)
        /\ live h0 okm /\ live h0 prk /\ live h0 info
        /\ B.all_disjoint [loc okm; loc prk; loc info]
    )
    (ensures fun h0 _ h1 ->
        // ImplHKDF.hash_block_length_fits a;
        modifies1 okm h0 h1
        /\ as_seq h1 okm == Spec.alg_hkdf_expand a (as_seq h0 prk) (as_seq h0 info) (size_v okm_len)
    )

inline_for_extraction noextract
val hkdf_expand_sha2_256:hkdf_expand_st SpecHash.SHA2_256

inline_for_extraction
let hkdf_expand (cs:Spec.supported_cipherSuite)
    = match (Spec.get_hash_alg cs) with
        | SpecHash.SHA2_256 -> hkdf_expand_sha2_256

/// ----------------- HKDF Extract
inline_for_extraction noextract
type hkdf_extract_st (a:Spec.hashAlg)
    = prk_out:alg_hash_out_buff a
    -> salt_len:size_t{size_v salt_len = Spec.alg_hash_size a}
    -> salt:lbuffer uint8 salt_len
    // Note that the requirement of `ikm_len` below is DIFFERENT from
    // the HACL's Spec. There are many inconsistencies between
    // preconditions of HACL spec and HACL impl.
    -> ikm_len:size_t{size_v ikm_len + DefHash.block_length a < pow2 32}
    -> ikm:lbuffer uint8 ikm_len
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 prk_out /\ live h0 salt /\ live h0 ikm
        /\ B.all_disjoint [loc prk_out; loc salt; loc ikm]
    )
    (ensures fun h0 _ h1 -> modifies1 prk_out h0 h1
        /\ as_seq h1 prk_out == Spec.alg_hkdf_extract a (as_seq h0 salt) (as_seq h0 ikm)
    )

inline_for_extraction noextract
val hkdf_extract_sha2_256:hkdf_extract_st SpecHash.SHA2_256

inline_for_extraction
let hkdf_extract (cs:Spec.supported_cipherSuite)
    = match (Spec.get_hash_alg cs) with
        | SpecHash.SHA2_256 -> hkdf_extract_sha2_256

(*-------------------- EC signature scheme*)

val split_P256_signature:
    sig:signature_buff
    -> ST.Stack (lbuffer uint8 (size 32) & lbuffer uint8 (size 32))
    (requires fun h0 -> live h0 sig)
    (ensures fun h0 (r,s) h1 -> modifies0 h0 h1
        /\ as_seq h1 r == Seq.sub (as_seq h0 sig) 0 32
        /\ as_seq h1 s == Seq.sub (as_seq h0 sig) 32 32 
        /\ Seq.equal (as_seq h1 sig) (Seq.concat (as_seq h1 r) (as_seq h1 s))
    )

/// EC-Signing

inline_for_extraction noextract
type ecdsa_sign_st (sa:Spec.signatureAlg) (ha:Spec.hashAlg)
    = signature:signature_buff
    -> nonce:option (lbuffer uint8 32ul)
    -> msg_len:size_t{size_v msg_len >= Spec.P256.min_input_length (Spec.P256.Hash ha)
                    /\ size_v msg_len <= max_size_t}
    -> msg:lbuffer uint8 msg_len
    -> priv:alg_ecdsa_priv_key_buf sa
    -> ST.Stack bool
    (requires fun h0 ->
        live h0 signature /\ live h0 msg /\ live h0 priv
        /\ B.all_disjoint [loc signature; loc priv; loc msg]
        /\ (
            // require that the caller must provide nonce if they use Es256
            match sa with
            | SpecDH.DH_P256 -> (
                match nonce with
                    | None -> False
                    | Some nonce_buffer -> (
                        live h0 nonce_buffer /\ disjoint nonce_buffer msg /\ disjoint nonce_buffer priv
                        /\ disjoint nonce_buffer signature 
                    )
            )
            | SpecDH.DH_Curve25519 -> not (Some? nonce)
        )
    )
    (ensures fun h0 res h1 -> modifies1 signature h0 h1
        /\ (
            let op_nonce = match nonce with
                            | Some v -> Some (as_seq h0 v)
                            | None -> None
                            in
            let spec_sig = Spec.alg_ecdsa_sign sa ha op_nonce (as_seq h0 msg) (as_seq h0 priv) in
            (res <==> Some? spec_sig)
            /\ (res ==> as_seq h1 signature == Some?.v spec_sig)
        )
    )

val ecdsa_sign (cs:Spec.supported_cipherSuite)
    :ecdsa_sign_st (Spec.get_signature_alg cs) (Spec.get_hash_alg cs)

/// EC-Verification
inline_for_extraction noextract
type ecdsa_verify_st (sa:Spec.signatureAlg) (ha:Spec.hashAlg)
    = msg_len:size_t{size_v msg_len >= Spec.P256.min_input_length (Spec.P256.Hash ha)
                    /\ size_v msg_len <= max_size_t}
    -> msg:lbuffer uint8 msg_len
    -> pub:alg_ecdsa_pub_key_buf sa
    -> signature:signature_buff
    -> ST.Stack bool
    (requires fun h0 -> 
        live h0 msg /\ live h0 pub /\ live h0 signature
        /\ B.all_disjoint [loc msg; loc pub; loc signature]
    )
    (ensures fun h0 res h1 -> modifies0 h0 h1
        /\ res == Spec.alg_ecdsa_verify sa ha (as_seq h0 msg) (as_seq h0 pub) (as_seq h0 signature)
    )

inline_for_extraction
val ecdsa_verify (cs:Spec.supported_cipherSuite)
    :ecdsa_verify_st (Spec.get_signature_alg cs) (Spec.get_hash_alg cs)

(*-------------------- XOR*)
val xor_buffer:
    #len:size_t{size_v len <= max_size_t}
    -> output:lbuffer uint8 len
    -> b1:lbuffer uint8 len
    -> b2:lbuffer uint8 len
    -> ST.Stack unit
    (requires fun h0 ->
        live h0 b1 /\ live h0 b2 /\ live h0 output
        /\ B.all_disjoint [loc b1; loc b2; loc output]
    )
    (ensures fun h0 _ h1 -> modifies1 output h0 h1
        /\ as_seq h1 output == Spec.xor (as_seq h0 b1) (as_seq h0 b2)
    )

(*-------------------- Generate key pairs*)
val generate_ec_keypair:
    cs:Spec.supported_cipherSuite
    -> priv:ec_priv_key_buf cs
    -> pub:ec_pub_key_buf cs
    -> ST.Stack bool
    (requires fun h0 ->
        live h0 pub /\ live h0 priv /\ live h0 entropy_p
        /\ B.all_disjoint [loc priv; loc pub; loc entropy_p]
    )
    (ensures fun h0 res h1 ->
        modifies3 pub priv entropy_p h0 h1 /\
        (
            let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
            let e1_v = B.deref h1 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in
            let res_abstract = Spec.generate_ec_keypair cs e0_v in

            (res <==> Some? res_abstract) /\
            (res ==> (
                let (keypair_abstract, entr1) = Some?.v res_abstract in

                Seq.equal keypair_abstract.priv (as_seq h1 priv)
                /\ Seq.equal keypair_abstract.pub (as_seq h1 pub)
                /\ entr1 == Ghost.reveal e1_v
            ))
        )
    )