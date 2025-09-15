module Impl.KEMEDHOC.TranscriptHash

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
module Spec = Spec.KEMEDHOC.TranscriptHash

open Impl.KEMEDHOC.CryptoPrimitives
open Impl.KEMEDHOC.Types
open Impl.KEMEDHOC.Parser


/// Transcript Hash 1
val compute_th1:
  #kcs: supportedKemCipherSuite
  -> pk_X: kem_pub_key_buff kcs
  -> ct_auth_R: kem_ciphertext_buff kcs
  -> th1: hash_out_buff kcs
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 pk_X /\ live h0 ct_auth_R /\ live h0 th1
    /\ B.all_disjoint [loc pk_X; loc ct_auth_R; loc th1]
  )
  (ensures fun h0 _ h1 ->
    let th1_s = Spec.compute_th1 #kcs (as_seq h0 pk_X) (as_seq h0 ct_auth_R) in

    modifies1 th1 h0 h1
    /\ Seq.equal (as_seq h1 th1) th1_s
  )

/// Transcript Hash 2
val compute_th2:
  #kcs: supportedKemCipherSuite
  -> ct_y: kem_ciphertext_buff kcs
  -> k_auth_I: kem_shared_secret_buff kcs
  -> msg1: message1 kcs
  -> th2: hash_out_buff kcs
  -> ST.Stack unit
  (requires fun h0 -> is_legit_message1 h0 msg1
    /\ is_valid_message1 h0 msg1 /\ live h0 ct_y /\ live h0 k_auth_I /\ live h0 th2
    /\ B.all_disjoint [loc ct_y; loc k_auth_I; loc th2; message1_union msg1]
  )
  (ensures fun h0 _ h1 ->
    let th2_s = Spec.compute_th2 #kcs (as_seq h0 ct_y) (as_seq h0 k_auth_I) (message1_eval h0 msg1) in

    modifies1 th2 h0 h1
    /\ Seq.equal (as_seq h1 th2) th2_s
  )

val compute_th2_pre_hash:
  #kcs: supportedKemCipherSuite
  -> ct_y: kem_ciphertext_buff kcs
  -> k_auth_I: kem_shared_secret_buff kcs
  -> msg1_hash: hash_out_buff kcs
  -> th2: hash_out_buff kcs
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 ct_y /\ live h0 k_auth_I /\ live h0 msg1_hash /\ live h0 th2
    /\ B.all_disjoint [loc ct_y; loc k_auth_I; loc msg1_hash; loc th2]
  )
  (ensures fun h0 _ h1 ->
    let th2_s = Spec.compute_th2_pre_hash #kcs (as_seq h0 ct_y) (as_seq h0 k_auth_I) (as_seq h0 msg1_hash) in

    modifies1 th2 h0 h1
    /\ Seq.equal (as_seq h1 th2) th2_s
  )

/// Transcript Hash 3
val compute_th3:
  #kcs: supportedKemCipherSuite
  -> th2: hash_out_buff kcs
  -> ptx2: plaintext2 kcs
  -> cred_r: cred_buffer
  -> th3: hash_out_buff kcs
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_plaintext2 h0 ptx2 /\ live h0 th2 /\ live h0 cred_r /\ live h0 th3
    /\ B.all_disjoint [loc th2; loc cred_r; loc th3; plaintext2_union ptx2]
  )
  (ensures fun h0 _ h1 ->
    let th3_s = Spec.compute_th3 #kcs (as_seq h0 th2) (plaintext2_eval h0 ptx2) (as_seq h0 cred_r) in

    modifies1 th3 h0 h1
    /\ Seq.equal (as_seq h1 th3) th3_s
  )

/// Transcript Hash 4
val compute_th4:
  #kcs: supportedKemCipherSuite
  -> th3 : hash_out_buff kcs
  -> ptx3 : plaintext3 kcs
  -> cred_i : cred_buffer
  -> th4 : hash_out_buff kcs
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_plaintext3 h0 ptx3 /\ live h0 th3 /\ live h0 cred_i /\ live h0 th4
    /\ B.all_disjoint [loc th3; loc cred_i; loc th4; plaintext3_union ptx3]
  )
  (ensures fun h0 _ h1 ->
    let th4_s = Spec.compute_th4 #kcs (as_seq h0 th3) (plaintext3_eval h0 ptx3) (as_seq h0 cred_i) in

    modifies1 th4 h0 h1
    /\ Seq.equal (as_seq h1 th4) th4_s
  )