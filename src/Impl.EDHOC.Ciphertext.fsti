module Impl.EDHOC.Ciphertext

(*HACL modules*)
open Lib.Buffer
// open Lib.Sequence
open Lib.RawIntTypes
open Lib.IntTypes
open Lib.ByteSequence
module Seq = Lib.Sequence

(*LowStar modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq

open Impl.EDHOC.CryptoPrimitives
open Impl.EDHOC.Parser
open Impl.EDHOC.KeySchedule
open TypeHelper.EDHOC

open Spec.EDHOC.Base.Definitions

module Spec = Spec.EDHOC.Ciphertext
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecParser = Spec.EDHOC.Parser
module SpecSerd = Spec.EDHOC.Serialization

/// Ciphertext 2
val encrypt_plaintext2_mem:
  #cs:SpecCrypto.supported_cipherSuite
  -> #auth_material:SpecCrypto.authentication_material
  -> #len_ptx2:size_t
  -> ptx2_mem:plaintext2_mem #cs #auth_material{
    len_ptx2 = plaintext2_mem_get_length ptx2_mem
  }
  -> th2_buff:hash_out_buff cs
  -> prk2e_buff:hash_out_buff cs
  -> ciphertext2_buff:lbuffer uint8 len_ptx2
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_plaintext2_mem h0 ptx2_mem /\ live h0 th2_buff /\ live h0 prk2e_buff
    /\ live h0 ciphertext2_buff
    /\ B.all_disjoint [loc th2_buff; loc prk2e_buff; loc ciphertext2_buff]
    /\ plaintext2_mem_disjoint_to_buffer ptx2_mem ciphertext2_buff
  )
  (ensures fun h0 _ h1 -> (
    let ptx2_abstract = plaintext2_mem_to_plaintext2 h0 ptx2_mem in
    let th2 = as_seq h0 th2_buff in
    let prk2e = as_seq h0 prk2e_buff in
    let c2 = Spec.encrypt_plaintext2 ptx2_abstract th2 prk2e in

    modifies1 ciphertext2_buff h0 h1
    /\ Seq.equal c2 (as_seq h1 ciphertext2_buff)
  ))

val decrypt_ciphertext2:
  #cs:SpecCrypto.supported_cipherSuite
  -> #auth_material:SpecCrypto.authentication_material
  -> #len_c2:size_t
  -> c2_buff:ciphertext2_buff cs auth_material{
    length c2_buff = size_v len_c2
  }
  -> th2_buff:hash_out_buff cs
  -> prk2e_buff:hash_out_buff cs
  -> p2_buff:lbuffer uint8 len_c2
  -> ST.Stack unit
  (requires fun h0 -> 
    live h0 c2_buff /\ live h0 th2_buff /\ live h0 prk2e_buff /\ live h0 p2_buff
    /\ B.all_disjoint [loc c2_buff; loc th2_buff; loc prk2e_buff; loc p2_buff]
  )
  (ensures fun h0 _ h1 -> (
    let th2 = as_seq h0 th2_buff in
    let prk2e = as_seq h0 prk2e_buff in
    let c2 = as_seq h0 c2_buff in
    let p2_abstract = Spec.decrypt_ciphertext2 #cs #auth_material c2 th2 prk2e in

    modifies1 p2_buff h0 h1
    /\ Seq.equal p2_abstract (as_seq h1 p2_buff)
  ))


/// Ciphertext 3

/// This low-level model does return a response code `c_response`
/// indicating whether the operation succeeds. The failure can come
/// from the hardware configuration which this implementation is compiled
/// to. If the hardware does not support Vale's instructions, it will
/// return an error. Note that the high-level, FStar, does not cover
/// this implementation-specific error, so it does not have error code
/// as returning.
val encrypt_plaintext3:
  #cs:SpecCrypto.supported_cipherSuite
  -> #auth_material:SpecCrypto.authentication_material
  -> len_ptx3:size_t{
    let aead_alg = (SpecCrypto.get_aead_alg cs) in
    size_v len_ptx3 + (SpecCrypto.aead_tag_size aead_alg) <= max_size_t
    /\ size_v len_ptx3 <= (SpecCrypto.alg_aead_max_input_size aead_alg)
  }
  -> ptx3_mem:plaintext3_mem #cs #auth_material{
    len_ptx3 = plaintext3_mem_get_length ptx3_mem
  }
  -> th3_buff:hash_out_buff cs
  -> prk3e2m_buff:hash_out_buff cs
  -> c3_buff:lbuffer uint8 (len_ptx3
    +! size (SpecCrypto.aead_tag_size (SpecCrypto.get_aead_alg cs)))
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_plaintext3_mem h0 ptx3_mem /\ live h0 th3_buff /\ live h0 prk3e2m_buff /\ live h0 c3_buff
    /\ B.all_disjoint [loc th3_buff; loc prk3e2m_buff; loc c3_buff]
    /\ plaintext3_mem_disjoint_to_buffer ptx3_mem c3_buff
  )
  (ensures fun h0 res h1 -> (
    let th3 = as_seq h0 th3_buff in
    let prk3e2m = as_seq h0 prk3e2m_buff in
    let p3_abstract = plaintext3_mem_to_plaintext3 h0 ptx3_mem in
    let c3_abstract
      = Spec.encrypt_plaintext3 #cs #auth_material p3_abstract th3 prk3e2m in

    match res with
      | CSuccess ->
        modifies1 c3_buff h0 h1 /\ Seq.equal c3_abstract (as_seq h1 c3_buff)
      | CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | _ -> False
  ))

val decrypt_ciphertext3:
  #cs:SpecCrypto.supported_cipherSuite
  -> #auth_material:SpecCrypto.authentication_material
  -> #len_c3:size_t{
    let tag_size = SpecCrypto.aead_tag_size (SpecCrypto.get_aead_alg cs) in
    len_c3 = plaintext3_len_fixed_v cs auth_material +! size tag_size
    }
  -> c3_buff:lbuffer uint8 len_c3
  -> th3_buff:hash_out_buff cs
  -> prk3e2m_buff:hash_out_buff cs
  -> p3_buff:lbuffer uint8 (plaintext3_len_fixed_v cs auth_material)
  -> ST.Stack c_response
  (requires fun h0 ->
    live h0 c3_buff /\ live h0 th3_buff /\ live h0 prk3e2m_buff /\ live h0 p3_buff
    /\ B.all_disjoint [loc c3_buff; loc th3_buff; loc prk3e2m_buff; loc p3_buff]
  )
  (ensures fun h0 cres h1 -> (
    let th3 = as_seq h0 th3_buff in
    let prk3e2m = as_seq h0 prk3e2m_buff in
    let c3 = as_seq h0 c3_buff in
    let res_abstract
      = Spec.decrypt_ciphertext3 #cs auth_material c3 th3 prk3e2m in

    (match cres with
      | CSuccess -> 
        modifies1 p3_buff h0 h1
        /\ (
          match res_abstract with
          | Res p3_abstract -> Seq.equal p3_abstract (as_seq h1 p3_buff)
          | _ -> False
        )
      | CDecryptionFailure -> res_abstract == Fail DecryptionFailed
      | CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | _ -> False
    )
  ))