module Impl.KEMEDHOC.Types

open Lib.ByteBuffer
open Lib.Buffer
open Lib.IntTypes
open Lib.ByteSequence
open LowStar.BufferOps

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module SpecParser = Spec.KEMEDHOC.Parser

open Spec.KEMEDHOC.CryptoPrimitives
// module ImplEdhocCrypto = Impl.EDHOC.CryptoPrimitives
module SpecEdhocCrypto = Spec.EDHOC.CryptoPrimitives
module SpecEdhocSerd = Spec.EDHOC.Serialization
module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives

open Impl.EDHOC.Utilities

/// The Low* type that represents an optional
/// lbytes sequence
noeq type lbufferOpt (len: size_t) = {
  is_some: lbuffer uint8 1ul;
  value: lbuffer uint8 len
}

let lbufferOpt_is_Some (#len: size_t)
  (h: HS.mem) (buff: lbufferOpt len)
  : GTot bool
  = SpecEdhocSerd.bytes_to_nat (as_seq h buff.is_some) = 1

let lbufferOpt_is_None (#len: size_t)
  (h: HS.mem) (buff: lbufferOpt len)
  : GTot bool
  = SpecEdhocSerd.bytes_to_nat (as_seq h buff.is_some) = 0

let lbufferOpt_live (#len: size_t)
  (h: HS.mem) (buff: lbufferOpt len)
  = live h buff.value /\ live h buff.is_some

let lbufferOpt_disjoint (#len: size_t)
  (buff: lbufferOpt len)
  = disjoint buff.value buff.is_some

let is_valid_lbufferOpt (#len: size_t)
  (h: HS.mem) (buff: lbufferOpt len)
  = lbufferOpt_live h buff /\ lbufferOpt_disjoint buff
  /\ (lbufferOpt_is_Some h buff \/ lbufferOpt_is_None h buff)

let is_legit_lbufferOpt (#len: size_t)
  (h: HS.mem) (buff: lbufferOpt len)
  = is_valid_lbufferOpt h buff
  /\ (lbufferOpt_is_Some h buff \/ lbufferOpt_is_None h buff)

inline_for_extraction
type valid_lbufferOpt (#len: size_t) (h: HS.mem)
  = bo: lbufferOpt len{ is_valid_lbufferOpt h bo }

let lbufferOpt_disjoint_to_lbuff (#t: buftype) (#a: Type0)
  (#len: size_t) (buff: lbufferOpt len) (b: buffer_t t a)
  = disjoint buff.value b /\ disjoint buff.is_some b

let lbufferOpt_loc (#len: size_t)
  (buff: lbufferOpt len)
  = loc buff.value |+| loc buff.is_some

let lbufferOpt_set_Some (#len: size_t)
  (buff_opt: lbufferOpt len)
  : ST.Stack unit
  (requires fun h0 ->
    is_valid_lbufferOpt h0 buff_opt
  )
  (ensures fun h0 _ h1 ->
    modifies1 buff_opt.is_some h0 h1
    /\ SpecEdhocSerd.bytes_to_nat (as_seq h1 buff_opt.is_some) = 1
  )
  = nat_to_bytes 1ul buff_opt.is_some 1

let lbufferOpt_set_None (#len: size_t)
  (buff_opt: lbufferOpt len)
  : ST.Stack unit
  (requires fun h0 ->
    is_valid_lbufferOpt h0 buff_opt
  )
  (ensures fun h0 _ h1 ->
    modifies1 buff_opt.is_some h0 h1
    /\ SpecEdhocSerd.bytes_to_nat (as_seq h1 buff_opt.is_some) = 0
  )
  = nat_to_bytes 1ul buff_opt.is_some 0

/// Convert lbuffer_opt to `option lbytes`
/// only for proofs
let eval_lbuffer_opt (#len: size_t)
  (h: HS.mem) (buff: valid_lbufferOpt #len h)
  : GTot (option (lbytes (size_v len)))
  = if (lbufferOpt_is_Some h buff)
    then Some (as_seq h buff.value)
    else None

let lemma_lbufferOpt_is_Some_equiv (#len: size_t)
  (h: HS.mem) (buff: lbufferOpt len)
  : Lemma (requires is_valid_lbufferOpt h buff)
  (ensures lbufferOpt_is_Some h buff <==> Option.isSome (eval_lbuffer_opt h buff))
  [SMTPat (lbufferOpt_is_Some h buff)]
  = ()

let lemma_lbufferOpt_is_None_equiv (#len: size_t)
  (h: HS.mem) (buff: lbufferOpt len)
  : Lemma (requires is_valid_lbufferOpt h buff)
  (ensures lbufferOpt_is_None h buff <==> Option.isNone (eval_lbuffer_opt h buff))
  [SMTPat (lbufferOpt_is_None h buff)]
  = ()

(*EDHOC message buffers*)

/// Plaintext buffers
inline_for_extraction
type plaintext1_buff = lbuffer uint8 (size SpecParser.plaintext1_size)
inline_for_extraction
type plaintext2_buff (kcs: supportedKemCipherSuite)
  = lbuffer uint8 (size (SpecParser.plaintext2_size kcs))
inline_for_extraction
type plaintext3_buff (kcs: supportedKemCipherSuite)
  = lbuffer uint8 (size (SpecParser.plaintext3_size kcs))

/// Ciphertext buffers
inline_for_extraction
type c1_buff (kcs: supportedKemCipherSuite)
  = lbuffer uint8 (size (SpecParser.c1_size kcs))
inline_for_extraction
type c2_buff (kcs: supportedKemCipherSuite)
  = lbuffer uint8 (size (SpecParser.c2_size kcs))
inline_for_extraction
type c3_buff (kcs: supportedKemCipherSuite)
  = lbuffer uint8 (size (SpecParser.c3_size kcs))

(*Crypto Primitives buffer*)

/// Alg-driven KEM buffers
inline_for_extraction
type alg_kem_pub_key_buff (a: kemAlg)
  = lbuffer uint8 (size (alg_kem_public_key_size a))
inline_for_extraction
type alg_kem_priv_key_buff (a: kemAlg)
  = lbuffer uint8 (size (alg_kem_priv_key_size a))
inline_for_extraction
type alg_kem_ciphertext_buff (a: kemAlg)
  = lbuffer uint8 (size (alg_kem_ciphertext_size a))
inline_for_extraction
type alg_kem_shared_secret_buff (a: kemAlg)
  = lbuffer uint8 (size (alg_kem_shared_secret_size a))

/// Ciphersuite-driven KEM buffers
inline_for_extraction
let kem_public_key_size_t (kcs: kemCipherSuite)
  = size (kem_public_key_size kcs)
inline_for_extraction
let kem_priv_key_size_t (kcs: kemCipherSuite)
  = size (kem_priv_key_size kcs)
inline_for_extraction
let kem_ciphertext_size_t (kcs: kemCipherSuite)
  = size (kem_ciphertext_size kcs)
inline_for_extraction
let kem_shared_secret_size_t (kcs: kemCipherSuite)
  = size (kem_shared_secret_size kcs)


inline_for_extraction
let hash_size_t (kcs: kemCipherSuite)
  = size (hash_size kcs)

inline_for_extraction
type kem_pub_key_buff (kcs: kemCipherSuite)
  = alg_kem_pub_key_buff (get_kem_alg kcs)
inline_for_extraction
type kem_priv_key_buff (kcs: kemCipherSuite)
  = alg_kem_priv_key_buff (get_kem_alg kcs)
inline_for_extraction
type kem_ciphertext_buff (kcs: kemCipherSuite)
  = alg_kem_ciphertext_buff (get_kem_alg kcs)
inline_for_extraction
type kem_shared_secret_buff (kcs: kemCipherSuite)
  = alg_kem_shared_secret_buff (get_kem_alg kcs)

/// KEM key pair types
inline_for_extraction
type kem_key_pair_m (kcs: kemCipherSuite) = kem_pub_key_buff kcs & kem_priv_key_buff kcs
inline_for_extraction
let get_pub_kem_key_m (#kcs: kemCipherSuite) (kp: kem_key_pair_m kcs)
  : (kem_pub_key_buff kcs)
  = match kp with | pub, _ -> pub
let get_priv_kem_key_m (#kcs: kemCipherSuite) (kp: kem_key_pair_m kcs)
  : (kem_priv_key_buff kcs)
  = match kp with | _, priv -> priv

let kem_key_pair_m_eval (#kcs: supportedKemCipherSuite)
  (h: HS.mem) (kp: kem_key_pair_m kcs)
  : GTot (SpecCrypto.kemKeyPair kcs)
  = match kp with
    | (pk, sk) -> (as_seq h pk, as_seq h sk)


/// Hash out buffer
// inline_for_extraction
// type alg_hash_out_buff ()
inline_for_extraction
type hash_out_buff (kcs: kemCipherSuite)
  = lbuffer uint8 (size (hash_size kcs))


/// AEAD buffers
inline_for_extraction
type aead_tag_buff (kcs: kemCipherSuite)
  = lbuffer uint8 (size (aead_tag_size kcs))
inline_for_extraction
type aead_iv_buff
  = lbuffer uint8 (size aead_iv_size)
inline_for_extraction
type aead_key_buff (kcs: kemCipherSuite)
  = lbuffer uint8 (size (aead_key_size kcs))
inline_for_extraction
type aead_valid_input_buff (kcs: kemCipherSuite)
  = b:buffer_t MUT uint8{
    length b <= SpecEdhocCrypto.alg_aead_max_input_size (get_aead_alg kcs)
  }
inline_for_extraction
type aead_valid_ciphertext_buff (kcs: kemCipherSuite)
  = b:buffer_t MUT uint8{
    let tag_size = aead_tag_size kcs in
    length b >= tag_size
    /\ length b <= SpecEdhocCrypto.alg_aead_max_input_size (get_aead_alg kcs) + tag_size
  }

/// MAC23 buffer
inline_for_extraction
type mac23_buff (kcs: supportedKemCipherSuite)
  = lbuffer uint8 (size (mac23_size kcs))