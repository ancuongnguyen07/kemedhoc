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

/// The Low* type that represents an optional
/// lbytes sequence
noeq type lbufferOpt (len: size_t) = {
  is_some: bool;
  value: lbuffer uint8 len
}

/// Convert lbuffer_opt to `option lbytes`
/// only for proofs
let eval_lbuffer_opt (#len: size_t)
  (h: HS.mem) (buff: lbufferOpt len)
  : GTot (option (lbytes (size_v len)))
  = if (buff.is_some)
    then Some (as_seq h buff.value)
    else None

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
type kem_pub_key_buff (kcs: kemCipherSuite)
  = alg_kem_pub_key_buff (get_kem_alg kcs)
inline_for_extraction
type kem_priv_key_buff (kcs: kemCipherSuite)
  = alg_kem_priv_key_buff (get_kem_alg kcs)
inline_for_extraction
type kem_ciphertext_buff (kcs: kemCipherSuite)
  = alg_kem_ciphertext_buff (get_kem_alg kcs)
inline_for_extraction
type kem_shared_secret_size (kcs: kemCipherSuite)
  = alg_kem_shared_secret_buff (get_kem_alg kcs)


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