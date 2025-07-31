module TypeHelper.EDHOC

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

module ImplAEAD = EverCrypt.AEAD
module SpecParser = Spec.EDHOC.Parser
module SpecCrypto = Spec.EDHOC.CryptoPrimitives

open LowStar.BufferOps
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntTypes

open EverCrypt.Error
open FStar.Tactics

open Spec.EDHOC.CryptoPrimitives
open Spec.EDHOC.Base.Definitions

open Impl.EDHOC.Utilities

type c_response =
  | CSuccess
  | CDecryptionFailure
  | CUnspecifiedError
  | CUnsupportedCipherSuite
  | CUnsupportedAlgorithmOrInvalidConfig
  | CUnknownCredentialID
  | CMissingKey
  | CInvalidLength
  | CUnsupportedAuthenticationMethod
  | CInvalidECPoint
  | CSerializationDeserializationFailed
  | CSigningFailed
  | CIntegrityCheckFailed
  | CInvalidState
  | CInvalidCredential

let error_to_c_response (e:error)
  = match e with
    | UnspecifiedError -> CUnspecifiedError
    | UnsupportedCipherSuite -> CUnsupportedCipherSuite
    | UnknownCredentialID -> CUnknownCredentialID
    | MissingKey -> CMissingKey
    | InputSize -> CInvalidLength
    | DecryptionFailed -> CDecryptionFailure
    | UnsupportedAuthenticationMethod -> CUnsupportedAuthenticationMethod
    | InvalidECPoint -> CInvalidECPoint
    | SerializationDeserializationFailed -> CSerializationDeserializationFailed
    | SigningFailed -> CSigningFailed
    | IntegrityCheckFailed -> CIntegrityCheckFailed
    | InvalidState -> CInvalidState
    | InvalidCredential -> CInvalidCredential

inline_for_extraction noextract
let convert_subtype (#a1:Type) (#a2:Type{subtype_of a1 a2}) (x:a1) : a2 =
  x

let evercrypt_err_to_c_response (e:error_code)
  :c_response
  = match e with
    | Success -> CSuccess
    | InvalidKey | AuthenticationFailure -> CDecryptionFailure
    | UnsupportedAlgorithm -> CUnsupportedAlgorithmOrInvalidConfig 
    | _ -> CUnspecifiedError

/// fixed-length buffers
inline_for_extraction
type ead_buff = lbuffer_or_null uint8 (size SpecParser.ead_max_size)
inline_for_extraction
type c_id_buff = lbuffer uint8 (size SpecParser.c_id_size)
inline_for_extraction
type id_cred_buff = lbuffer uint8 (size SpecParser.id_cred_size)
inline_for_extraction
type cred_buff = lbuffer uint8 (size SpecParser.cred_size)
inline_for_extraction
type info_label_buff = lbuffer uint8 1ul
inline_for_extraction
type okm_len_type_buff = b:buffer_t MUT uint8{length #MUT #uint8 b <= 2}

inline_for_extraction
type method_buff = b:lbuffer uint8 1ul

inline_for_extraction
type suite_buff = b:lbuffer uint8 1ul

inline_for_extraction
let mac23_size_v (cs:supported_cipherSuite) (auth_material:authentication_material)
  = size (mac23_size cs auth_material)

inline_for_extraction
let sig_or_mac23_size_v (cs:supported_cipherSuite) (auth_material:authentication_material)
  = size (SpecParser.sig_or_mac23_size cs auth_material)

let lemma_sig_or_mac23_size_v_equiv (cs:supported_cipherSuite)
  (auth_material:authentication_material)
  : Lemma (ensures (
    let s = sig_or_mac23_size_v cs auth_material in
    match auth_material with
      | Signature -> size_v s = SpecCrypto.signature_size
      | MAC -> s = mac23_size_v cs auth_material
  ))
  [SMTPat (sig_or_mac23_size_v cs auth_material)]
  = ()


inline_for_extraction
type mac23_buff (cs:supported_cipherSuite) (auth_material:authentication_material)
  = lbuffer uint8 (mac23_size_v cs auth_material)

inline_for_extraction
type sig_or_mac23_buff (cs:supported_cipherSuite) (auth_material:authentication_material)
  = lbuffer uint8 (sig_or_mac23_size_v cs auth_material)

inline_for_extraction
type ciphertext2_buff (cs:supported_cipherSuite) (auth_material:authentication_material)
  // = b:buffer_t MUT uint8{SpecParser.is_valid_ptx2_cipher2_size cs auth_material (length b)}
  // NOTE! This model does not support EAD, so `min_ptx2_size` is used here
  // as EAD is excluded. `ead_max_size` should be set to 0
  = lbuffer uint8 (size (SpecParser.min_ptx2_size cs auth_material + SpecParser.ead_max_size))
inline_for_extraction
type plaintext2_buff (cs:supported_cipherSuite) (auth_material:authentication_material)
  = ciphertext2_buff cs auth_material

inline_for_extraction
type plaintext3_buff (cs:supported_cipherSuite) (auth_material:authentication_material)
  // = b:buffer_t MUT uint8{SpecParser.is_valid_ptx3_size cs auth_material (length b)}
  = lbuffer uint8 (size (SpecParser.min_ptx3_size cs auth_material + SpecParser.ead_max_size))

(*---------------- Hash*)
inline_for_extraction
type alg_hash_out_buff (a:hashAlg) = lbuffer uint8 (size (alg_hash_size a))
inline_for_extraction
type hash_out_buff (cs:supported_cipherSuite) = alg_hash_out_buff (get_hash_alg cs)
inline_for_extraction
type opt_hash_out_buff (cs:supported_cipherSuite)
  = lbuffer_or_null uint8 (size (alg_hash_size (get_hash_alg cs)))

(*------------------ AEAD*)
inline_for_extraction noextract
type aead_iv_lbuffer = lbuffer uint8 (size aead_iv_size)
inline_for_extraction noextract
type aead_key_lbuffer (a:aeadAlg) = lbuffer uint8 (size (aead_key_size a))
inline_for_extraction noextract
type aead_key_buff (cs:supported_cipherSuite) = aead_key_lbuffer (get_aead_alg cs)
inline_for_extraction noextract
type aead_tag_lbuffer (a:aeadAlg) = lbuffer uint8 (size (aead_tag_size a))

type alg_aead_ciphertext_buff (a:aeadAlg) = b:buffer_t MUT uint8{
  length b >= (aead_tag_size a)
  /\ length b <= Spec.Agile.AEAD.max_length a + (aead_tag_size a)
}
inline_for_extraction
type aead_ciphertext_buff (c:supported_cipherSuite) = alg_aead_ciphertext_buff (get_aead_alg c)


(*----------------- DH*)
// `size` converts `size_nat` to `size_t`
inline_for_extraction
let pub_key_size_v (cs:supported_cipherSuite)
  = size (ec_pub_key_size (get_ec_alg cs))
inline_for_extraction
let priv_key_size_v (cs:supported_cipherSuite)
  = size (ec_priv_key_size (get_ec_alg cs))
inline_for_extraction
let shared_secret_size_v (cs:supported_cipherSuite)
  = size (shared_secret_size cs)

inline_for_extraction
type ec_pub_key_buf (cs:supported_cipherSuite)
    = lbuffer uint8 (pub_key_size_v cs)

inline_for_extraction
type ec_priv_key_buf (cs:supported_cipherSuite)
    = lbuffer uint8 (priv_key_size_v cs)

inline_for_extraction
type shared_secret_buf (cs:supported_cipherSuite)
    = lbuffer uint8 (shared_secret_size_v cs)
inline_for_extraction
type opt_shared_secret_buf (cs:supported_cipherSuite)
  = lbuffer_or_null uint8 (shared_secret_size_v cs)

// optional buffer 'b' in which 'b' could be Null
inline_for_extraction
type opt_ec_pub_key_buf (cs:supported_cipherSuite)
    = lbuffer_or_null uint8 (pub_key_size_v cs)
inline_for_extraction
type opt_ec_priv_key_buf (cs:supported_cipherSuite)
    = lbuffer_or_null uint8 (priv_key_size_v cs)

/// Low-level model of `ec_keypair`
inline_for_extraction
type ec_keypair_mem (#cs:supported_cipherSuite)
    = ec_pub_key_buf cs & ec_priv_key_buf cs

// Optional `ec_keypair_mem`
inline_for_extraction
type opt_ec_keypair_mem (#cs:supported_cipherSuite)
    = opt_ec_pub_key_buf cs & opt_ec_priv_key_buf cs

// getters | optional getters
// pub getters
inline_for_extraction noextract
let ec_keypair_mem_get_pub (#cs:supported_cipherSuite)
    (keypair:ec_keypair_mem #cs)
    = match keypair with pub_buf, _ -> pub_buf
inline_for_extraction noextract
let opt_ec_keypair_mem_get_pub (#cs:supported_cipherSuite)
    (opt_keypair:opt_ec_keypair_mem #cs)
    = match opt_keypair with pub, priv -> pub

// eval pub getters
inline_for_extraction noextract
let eval_ec_keypair_mem_get_pub (#cs:supported_cipherSuite)
  (h:HS.mem) (keypair:ec_keypair_mem #cs)
  : GTot (ec_pub_key cs)
  = match keypair with pub, priv ->
    as_seq h pub
inline_for_extraction noextract
let eval_opt_ec_keypair_mem_get_pub (#cs:supported_cipherSuite)
  (h:HS.mem) (opt_keypair:opt_ec_keypair_mem #cs)
  : GTot (option (ec_pub_key cs))
  = match opt_keypair with pub, _ -> (
    if (g_is_null pub) then None
    else Some (nn_as_seq h pub)
  )

// priv getters
inline_for_extraction noextract
let ec_keypair_mem_get_priv (#cs:supported_cipherSuite)
    (keypair:ec_keypair_mem #cs)
    = match keypair with _, priv_buf -> priv_buf
inline_for_extraction noextract
let opt_ec_keypair_mem_get_priv (#cs:supported_cipherSuite)
    (opt_keypair:opt_ec_keypair_mem #cs)
    = match opt_keypair with pub, priv -> priv

// eval priv getters
inline_for_extraction noextract
let eval_ec_keypair_mem_get_priv (#cs:supported_cipherSuite)
  (h:HS.mem) (keypair:ec_keypair_mem #cs)
  : GTot (ec_priv_key cs)
  = match keypair with pub, priv ->
    as_seq h priv
inline_for_extraction noextract
let eval_opt_ec_keypair_mem_get_priv (#cs:supported_cipherSuite)
  (h:HS.mem) (opt_keypair:opt_ec_keypair_mem #cs)
  : GTot (option (ec_priv_key cs))
  = match opt_keypair with _, priv -> (
    if (g_is_null priv) then None
    else Some (nn_as_seq h priv)
  )

let unchanged_opt_ec_keypair_mem (#cs:supported_cipherSuite)
    (h0 h1:HS.mem) (opt_keypair:opt_ec_keypair_mem #cs)
    = match opt_keypair with pub, priv ->
        unchanged_lbuffer_or_null h0 h1 pub /\ unchanged_lbuffer_or_null h0 h1 priv

let g_is_null_opt_ec_keypair_mem (#cs:supported_cipherSuite)
  (opt_keypair:opt_ec_keypair_mem #cs)
  = match opt_keypair with pub, priv -> (
    g_is_null pub || g_is_null priv
  )

let g_is_total_null_opt_ec_keypair_mem (#cs:supported_cipherSuite)
  (opt_keypair:opt_ec_keypair_mem #cs)
  = match opt_keypair with pub, priv -> (
    g_is_null pub && g_is_null priv
  )

let g_is_same_state_opt_ec_keypair_mem (#cs:supported_cipherSuite)
  (opt_keypair:opt_ec_keypair_mem #cs)
  = match opt_keypair with pub, priv -> (
    g_is_null pub <==> g_is_null priv
  )

/// Convert computational model to abstract model of `ec_keypair`
let eval_ec_keypair_mem (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair:ec_keypair_mem #cs)
    : GTot (ec_keypair cs)
    = match keypair with pub_buf, priv_buf ->
      {
        pub = (as_seq h pub_buf);
        priv = (as_seq h priv_buf)
      }

let eval_opt_ec_keypair_mem (#cs:supported_cipherSuite)
    (h:HS.mem) (opt_keypair:opt_ec_keypair_mem #cs)
    : GTot (option (ec_keypair cs))
    = if (g_is_null_opt_ec_keypair_mem opt_keypair)
      then None
      else (
        match opt_keypair with opt_pub, opt_priv -> (
          assert(~(g_is_null opt_pub) /\ ~(g_is_null opt_priv));
          let res:ec_keypair cs =
          {
            pub = nn_as_seq h opt_pub;
            priv = nn_as_seq h opt_priv
          }
          in
          Some res
        )
      )

/// Return True if the computaional model and abstract model
/// of a given `ec_keypair` are equivalent
let is_equiv_ec_keypair_mem (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair_m:ec_keypair_mem #cs) (keypair_a:ec_keypair cs)
  = Seq.equal (keypair_a.pub) (eval_ec_keypair_mem_get_pub h keypair_m)
  /\ Seq.equal (keypair_a.priv) (eval_ec_keypair_mem_get_priv h keypair_m)

let lemma_opt_ec_keypair_mem_to_opt_ec_keypair (#cs:supported_cipherSuite)
    (h:HS.mem) (opt_keypair:opt_ec_keypair_mem #cs)
    : Lemma (ensures (
        let opt_keypair_abstract = eval_opt_ec_keypair_mem h opt_keypair in
        
        ~(g_is_null_opt_ec_keypair_mem opt_keypair) <==> (Some? opt_keypair_abstract)
        /\ (~(g_is_null_opt_ec_keypair_mem opt_keypair) ==> (
          match opt_keypair with opt_pub, opt_priv -> (
            let keypair_abstract_v = Some?.v opt_keypair_abstract in
            Seq.equal keypair_abstract_v.pub (nn_as_seq h opt_pub)
            /\ Seq.equal keypair_abstract_v.priv (nn_as_seq h opt_priv)
          ))
        )
    ))
    [SMTPat (eval_opt_ec_keypair_mem #cs h opt_keypair)]
    = ()

let lemma_ec_keypair_mem_to_ec_keypair_equiv (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair:ec_keypair_mem #cs)
    : Lemma (ensures (
        let ec_keypair_abstract = eval_ec_keypair_mem h keypair in
        match keypair with pub_buf, priv_buf ->
            Seq.equal (ec_keypair_abstract.pub) (as_seq h pub_buf)
            /\ Seq.equal (ec_keypair_abstract.priv) (as_seq h priv_buf)
    ))
    [SMTPat (eval_ec_keypair_mem #cs h keypair)]
    = ()

/// Predicates of `ec_keypair_mem`
let ec_keypair_mem_live (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair:ec_keypair_mem #cs)
    = match keypair with pub_buff, priv_buff ->
        live h pub_buff /\ live h priv_buff

let ec_keypair_mem_disjoint (#cs:supported_cipherSuite)
    (keypair:ec_keypair_mem #cs)
    = match keypair with pub_buff, priv_buff ->
        disjoint pub_buff priv_buff

let ec_keypair_mem_disjoint_to (#cs:supported_cipherSuite)
    (#t2:buftype) (#a2:Type0) (keypair:ec_keypair_mem #cs)
    (b2:buffer_t t2 a2)
    = match keypair with pub_buff, priv_buff ->
        B.all_disjoint [loc pub_buff; loc priv_buff; loc b2]

let is_valid_ec_keypair_mem (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair:ec_keypair_mem #cs)
    = ec_keypair_mem_live h keypair /\ ec_keypair_mem_disjoint keypair

let ec_keypair_mem_union_loc (#cs:supported_cipherSuite)
    (keypair:ec_keypair_mem #cs)
    = match keypair with pub_buff, priv_buff ->
        B.loc_union (loc pub_buff) (loc priv_buff)

/// Predicates of `opt_ec_keypair_mem`
/// Basically same as predicates for `ec_keypair_mem`
let opt_ec_keypair_mem_live (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair:opt_ec_keypair_mem #cs)
    = match keypair with pub_buff, priv_buff ->
        live h pub_buff /\ live h priv_buff

let opt_ec_keypair_mem_disjoint (#cs:supported_cipherSuite)
    (keypair:opt_ec_keypair_mem #cs)
    = match keypair with pub_buff, priv_buff ->
        disjoint pub_buff priv_buff

let opt_ec_keypair_mem_disjoint_to (#cs:supported_cipherSuite)
    (#t2:buftype) (#a2:Type0) (keypair:opt_ec_keypair_mem #cs)
    (b2:buffer_t t2 a2)
    = match keypair with pub_buff, priv_buff ->
        B.all_disjoint [loc pub_buff; loc priv_buff; loc b2]

let is_valid_opt_ec_keypair_mem (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair:opt_ec_keypair_mem #cs)
    = opt_ec_keypair_mem_live h keypair /\ opt_ec_keypair_mem_disjoint keypair

let opt_ec_keypair_mem_union_loc (#cs:supported_cipherSuite)
    (keypair:opt_ec_keypair_mem #cs)
    = match keypair with pub_buff, priv_buff ->
        B.loc_union (loc pub_buff) (loc priv_buff)

// let is_null_opt_ec_keypair_mem (#cs:supported_cipherSuite)
//   (opt_keypair:opt_ec_keypair_mem #cs)
//   : ST.Stack bool
//   (requires fun h0 -> is_valid_opt_ec_keypair_mem h0 opt_keypair)
//   (ensures fun h0 _ h1 -> modifies0 h0 h1)
//   = match opt_keypair with pub, priv -> (
//     is_null pub  is_null priv
//   )

/// Update function for `opt_ec_keypair_mem`
inline_for_extraction noextract
val update_opt_ec_keypair_mem:
  #cs:supported_cipherSuite
  -> kp_m:opt_ec_keypair_mem #cs
  -> pub_buff:opt_ec_pub_key_buf cs
  -> priv_buff:opt_ec_priv_key_buf cs
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_opt_ec_keypair_mem h0 kp_m /\ live h0 pub_buff /\ live h0 priv_buff
    /\ B.loc_disjoint (opt_ec_keypair_mem_union_loc kp_m) (B.loc_union (loc priv_buff) (loc pub_buff))
    // /\ opt_ec_keypair_mem_disjoint_to kp_m pub_buff
    /\ (g_is_null pub_buff <==> g_is_null priv_buff)
    /\ (match kp_m with opt_pub, opt_priv -> (
      (g_is_null opt_pub || g_is_null opt_priv ==> g_is_null priv_buff)
    ))
  )
  (ensures fun h0 _ h1 -> (
    if g_is_null priv_buff then modifies0 h0 h1
    else
      modifies (opt_ec_keypair_mem_union_loc kp_m) h0 h1
      /\ (~(g_is_null priv_buff) ==> (
        match kp_m with opt_pub, opt_priv ->
          Seq.equal (nn_as_seq h0 priv_buff) (nn_as_seq h1 opt_priv)
          /\ Seq.equal (nn_as_seq h0 pub_buff) (nn_as_seq h1 opt_pub)
      ))
  ))

(*-------------------------- EC Signature*)
inline_for_extraction
let sig_size_v = size signature_size
inline_for_extraction
type signature_buff = lbuffer uint8 sig_size_v
inline_for_extraction
type alg_ecdsa_pub_key_buf (a:signatureAlg)
    = lbuffer uint8 (size (ec_pub_key_size a))
inline_for_extraction
type ecdsa_pub_key_buf (cs:supported_cipherSuite)
    = alg_ecdsa_pub_key_buf (get_signature_alg cs)
inline_for_extraction
type alg_ecdsa_priv_key_buf (a:signatureAlg)
    = lbuffer uint8 (size (ec_priv_key_size a))
inline_for_extraction
type ecdsa_priv_key_buf (cs:supported_cipherSuite)
    = alg_ecdsa_priv_key_buf (get_signature_alg cs)

// optional types
inline_for_extraction
type opt_ecdsa_pub_key_buf (cs:supported_cipherSuite)
  = lbuffer_or_null uint8 (size (ec_pub_key_size (get_signature_alg cs)))
inline_for_extraction
type opt_ecdsa_priv_key_buf (cs:supported_cipherSuite)
  = lbuffer_or_null uint8 (size (ec_priv_key_size (get_signature_alg cs)))

/// Low-level model of `ec_signature_keypair`
inline_for_extraction
type ecdsa_sig_keypair_mem (#cs:supported_cipherSuite)
    = ecdsa_pub_key_buf cs & ecdsa_priv_key_buf cs
/// optional model
inline_for_extraction
type opt_ecdsa_sig_keypair_mem (#cs:supported_cipherSuite)
  = opt_ecdsa_pub_key_buf cs & opt_ecdsa_priv_key_buf cs

// getters and optional getters
// pub getters
inline_for_extraction noextract
let ecdsa_sig_keypair_mem_get_pub (#cs:supported_cipherSuite)
    (keypair:ecdsa_sig_keypair_mem #cs)
    = match keypair with pub_buff, _ -> pub_buff
inline_for_extraction noextract
let opt_ecdsa_sig_keypair_mem_get_pub (#cs:supported_cipherSuite)
  (keypair:opt_ecdsa_sig_keypair_mem #cs)
  = match keypair with pub, priv -> pub

// eval pub getters
inline_for_extraction noextract
let eval_ecdsa_sig_keypair_mem_get_pub (#cs:supported_cipherSuite)
  (h:HS.mem) (keypair:ecdsa_sig_keypair_mem #cs)
  : GTot (ec_signature_pub_key cs)
  = match keypair with pub, priv ->
    as_seq h pub
inline_for_extraction noextract
let eval_opt_ecdsa_sig_keypair_mem_get_pub (#cs:supported_cipherSuite)
  (h:HS.mem) (keypair:opt_ecdsa_sig_keypair_mem #cs)
  : GTot (option (ec_signature_pub_key cs))
  = match keypair with pub, priv -> (
    if (g_is_null pub) then None
    else Some (nn_as_seq h pub)
  )

// priv getters
inline_for_extraction noextract
let ecdsa_sig_keypair_mem_get_priv (#cs:supported_cipherSuite)
    (keypair:ecdsa_sig_keypair_mem #cs)
    = match keypair with _, priv_buff -> priv_buff
inline_for_extraction noextract
let opt_ecdsa_sig_keypair_mem_get_priv (#cs:supported_cipherSuite)
  (keypair:opt_ecdsa_sig_keypair_mem #cs)
  = match keypair with pub, priv -> priv

// eval priv getters
inline_for_extraction noextract
let eval_ecdsa_sig_keypair_mem_get_priv (#cs:supported_cipherSuite)
  (h:HS.mem) (keypair:ecdsa_sig_keypair_mem #cs)
  = match keypair with pub, priv ->
    as_seq h priv
inline_for_extraction noextract
let eval_opt_ecdsa_sig_keypair_mem_get_priv (#cs:supported_cipherSuite)
  (h:HS.mem) (keypair:opt_ecdsa_sig_keypair_mem #cs)
  : GTot (option (ec_signature_priv_key cs))
  = match keypair with pub, priv -> (
    if (g_is_null priv) then None
    else Some (nn_as_seq h priv)
  )

let is_null_opt_ecdsa_sig_keypair_mem (#cs:supported_cipherSuite)
  (keypair:opt_ecdsa_sig_keypair_mem #cs)
  = match keypair with pub, priv -> (
    g_is_null pub || g_is_null priv
  )

// Conversion between computational model and abstract model
inline_for_extraction noextract
let eval_ecdsa_sig_keypair_mem (#cs:supported_cipherSuite)
  (h:HS.mem) (keypair:ecdsa_sig_keypair_mem #cs)
  : GTot (ec_signature_keypair cs)
  = match keypair with pub_buff, priv_buff ->
      {
        pub = as_seq h pub_buff;
        priv = as_seq h priv_buff
      }

let eval_opt_ecdsa_sig_keypair_mem (#cs:supported_cipherSuite)
  (h:HS.mem) (opt_keypair:opt_ecdsa_sig_keypair_mem #cs)
  : GTot (option (ec_signature_keypair cs))
  = if (is_null_opt_ecdsa_sig_keypair_mem opt_keypair)
    then None
    else (
      match opt_keypair with opt_pub, opt_priv -> (
        assert(~(g_is_null opt_pub) /\ ~(g_is_null opt_priv));
        let res:ec_signature_keypair cs = {
          pub = nn_as_seq h opt_pub;
          priv = nn_as_seq h opt_priv
        } in
        Some res
      )
    )

/// Return True if the computaional model and abstract model
/// of a given `ec_signature_keypair` are equivalent
let is_equiv_ecdsa_sig_keypair_mem (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair_m:ecdsa_sig_keypair_mem #cs) (keypair_a:ec_signature_keypair cs)
  = Seq.equal (keypair_a.pub) (eval_ecdsa_sig_keypair_mem_get_pub h keypair_m)
  /\ Seq.equal (keypair_a.priv) (eval_ecdsa_sig_keypair_mem_get_priv h keypair_m)

let lemma_ecdsa_sig_keypair_mem_to_ec_sig_keypair_equiv (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair:ecdsa_sig_keypair_mem #cs)
    :Lemma (ensures (
        let keypair_abstract = eval_ecdsa_sig_keypair_mem h keypair in
        match keypair with pub_buff, priv_buff ->
            Seq.equal (keypair_abstract.pub) (as_seq h pub_buff)
            /\ Seq.equal (keypair_abstract.priv) (as_seq h priv_buff)
    ))
    [SMTPat (eval_ecdsa_sig_keypair_mem #cs h keypair)]
    = ()

let lemma_eval_opt_ecdsa_sig_keypair_mem_equiv (#cs:supported_cipherSuite)
  (h:HS.mem) (opt_keypair:opt_ecdsa_sig_keypair_mem #cs)
  : Lemma (ensures (
    let opt_sig_keypair_abstract = eval_opt_ecdsa_sig_keypair_mem h opt_keypair in
      ~(is_null_opt_ecdsa_sig_keypair_mem opt_keypair) <==> Some? opt_sig_keypair_abstract
      /\ (~(is_null_opt_ecdsa_sig_keypair_mem opt_keypair) ==> (
          match opt_keypair with opt_pub, opt_priv -> (
            let sig_keypair_abstract = Some?.v opt_sig_keypair_abstract in

            Seq.equal sig_keypair_abstract.pub (nn_as_seq h opt_pub)
            /\ Seq.equal sig_keypair_abstract.priv (nn_as_seq h opt_priv)
          )
      ))
  ))
  [SMTPat (eval_opt_ecdsa_sig_keypair_mem #cs h opt_keypair)]
  = ()

/// Predicates of `ecdsa_sig_keypair_mem`
let ecdsa_sig_keypair_mem_live (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair:ecdsa_sig_keypair_mem #cs)
    = match keypair with pub_buff, priv_buff ->
        live h pub_buff /\ live h priv_buff

let lemma_ecdsa_sig_keypair_mem_live (#cs:supported_cipherSuite)
  (h:HS.mem) (keypair:ecdsa_sig_keypair_mem #cs)
  : Lemma (ensures 
    ecdsa_sig_keypair_mem_live h keypair <==> (
      live h (ecdsa_sig_keypair_mem_get_priv keypair)
      /\ live h (ecdsa_sig_keypair_mem_get_pub keypair)
    )
  )
  [SMTPat (ecdsa_sig_keypair_mem_live h keypair)]
  = ()

let ecdsa_sig_keypair_mem_disjoint (#cs:supported_cipherSuite)
    (keypair:ecdsa_sig_keypair_mem #cs)
    = match keypair with pub_buff, priv_buff ->
        disjoint pub_buff priv_buff

let ecdsa_sig_keypair_mem_disjoint_to (#cs:supported_cipherSuite)
    (#t2:buftype) (#a2:Type0) (keypair:ecdsa_sig_keypair_mem #cs)
    (b2:buffer_t t2 a2)
    = match keypair with pub_buff, priv_buff ->
        B.all_disjoint [loc pub_buff; loc priv_buff; loc b2]

let is_valid_ecdsa_sig_keypair_mem (#cs:supported_cipherSuite)
    (h:HS.mem) (keypair:ecdsa_sig_keypair_mem #cs)
    = ecdsa_sig_keypair_mem_live h keypair /\ ecdsa_sig_keypair_mem_disjoint keypair

let ecdsa_sig_keypair_mem_union_loc (#cs:supported_cipherSuite)
    (keypair:ecdsa_sig_keypair_mem #cs)
    = match keypair with pub_buff, priv_buff ->
        B.loc_union (loc pub_buff) (loc priv_buff)