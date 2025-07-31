module Impl.EDHOC.TranscriptHash

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

open Spec.EDHOC.CryptoPrimitives
open Impl.EDHOC.Parser
open Impl.EDHOC.CryptoPrimitives
open TypeHelper.EDHOC

module Spec = Spec.EDHOC.TranscriptHash
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecParser = Spec.EDHOC.Parser
module SpecSerd = Spec.EDHOC.Serialization

/// Transcript Hash 2 (TH2)
val compute_th2_pre_hash_mem:
  #cs:supported_cipherSuite
  -> msg1_hash_m:hash_out_buff cs
  -> g_y_mem:ec_pub_key_buf cs
  -> th2_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 msg1_hash_m /\ live h0 g_y_mem /\ live h0 th2_buff
    /\ B.all_disjoint [loc msg1_hash_m; loc g_y_mem; loc th2_buff]
  )
  (ensures fun h0 _ h1 -> (

    modifies1 th2_buff h0 h1
    /\ Seq.equal (Spec.compute_th2_pre_hash #cs (as_seq h0 msg1_hash_m) (as_seq h0 g_y_mem))
                (as_seq h1 th2_buff)
  ))

val compute_th2_mem:
  #cs:supported_cipherSuite
  -> #msg1_len:size_t 
  // -> #g_y_len:size_t{size_v g_y_len = ec_pub_key_size (get_ec_alg cs)}
  -> msg1:message1_mem #cs{
    msg1_len = message1_mem_get_length msg1
  }
  -> g_y_mem:ec_pub_key_buf cs
  -> th2_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 g_y_mem /\ live h0 th2_buff /\ is_valid_message1_mem_after_init h0 msg1
    /\ disjoint th2_buff g_y_mem /\ message1_mem_disjoint_to msg1 th2_buff
  )
  (ensures fun h0 _ h1 ->
    (
      let msg1_abstract = eval_message1_mem #cs h0 msg1 in
      let g_y = as_seq h0 g_y_mem in

      modifies1 th2_buff h0 h1
      /\ Seq.equal (Spec.compute_th2 msg1_abstract g_y) (as_seq h1 th2_buff)
    )
  )

/// Transcript Hash 3 (TH3)
val compute_th3_mem:
  #cs:supported_cipherSuite
  -> auth_material:authentication_material
  // -> #len_ptx2:size_t
  -> th2_buff:hash_out_buff cs
  -> ptx2_mem:plaintext2_mem #cs #auth_material
  -> cred_r_buff:cred_buff
  -> th3_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 th2_buff /\ is_valid_plaintext2_mem h0 ptx2_mem /\ live h0 cred_r_buff
    /\ live h0 th3_buff /\ disjoint th3_buff th2_buff /\ disjoint th3_buff cred_r_buff
    /\ plaintext2_mem_disjoint_to_buffer ptx2_mem th3_buff
  )
  (ensures fun h0 _ h1 -> (
    let ptx2_abstract = plaintext2_mem_to_plaintext2 h0 ptx2_mem in
    let th2 = as_seq h0 th2_buff in
    let cred_r = as_seq h0 cred_r_buff in

    modifies1 th3_buff h0 h1
    /\ Seq.equal (Spec.compute_th3 th2 ptx2_abstract cred_r) (as_seq h1 th3_buff)
  ))

/// Transcript Hash 4 (TH4)
val compute_th4_mem:
  #cs:supported_cipherSuite
  -> auth_material:authentication_material
  // -> #len_ptx3:size_t
  -> th3_buff:hash_out_buff cs
  -> ptx3_mem:plaintext3_mem #cs #auth_material
  -> cred_i_buff:cred_buff
  -> th4_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 th3_buff /\ is_valid_plaintext3_mem h0 ptx3_mem /\ live h0 cred_i_buff
    /\ live h0 th4_buff /\ disjoint th4_buff th3_buff /\ disjoint th4_buff cred_i_buff
    /\ plaintext3_mem_disjoint_to_buffer ptx3_mem th4_buff
  )
  (ensures fun h0 _ h1 -> (
    let ptx3_abstract = plaintext3_mem_to_plaintext3 h0 ptx3_mem in
    let th3 = as_seq h0 th3_buff in
    let cred_i = as_seq h0 cred_i_buff in

    modifies1 th4_buff h0 h1
    /\ Seq.equal (Spec.compute_th4 th3 ptx3_abstract cred_i) (as_seq h1 th4_buff)
  )) 
