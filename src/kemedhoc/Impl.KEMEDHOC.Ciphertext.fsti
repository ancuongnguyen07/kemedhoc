module Impl.KEMEDHOC.Ciphertext

(*LowStar related modules*)
open Lib.ByteBuffer
open Lib.IntTypes
open Lib.Buffer

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module Spec = Spec.KEMEDHOC.Ciphertext
module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives

(*EDHOC utilities*)
open Impl.EDHOC.Utilities

(*KEMEDHOC utilities*)
open Impl.KEMEDHOC.Types
open Impl.KEMEDHOC.CryptoPrimitives
open Impl.KEMEDHOC.KeySchedule
open Impl.KEMEDHOC.Parser
open Spec.KEMEDHOC.Base.Definitions

module TypeEdhoc = TypeHelper.EDHOC

/// -------------
/// Ciphertext 1
/// -------------
val encrypt_plaintext1:
  #kcs: supportedKemCipherSuite
  -> ptx1: plaintext1
  -> th1: hash_out_buff kcs
  -> prk1e: hash_out_buff kcs
  -> c1: c1_buff kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_plaintext1 h0 ptx1 /\ live h0 th1 /\ live h0 prk1e /\ live h0 c1
    /\ B.all_disjoint [plaintext1_union ptx1; loc th1; loc prk1e; loc c1]
  )
  (ensures fun h0 res h1 ->
    let c1_s = Spec.encrypt_plaintext1 #kcs (plaintext1_eval h0 ptx1) (as_seq h0 th1) (as_seq h0 prk1e) in

    match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CSuccess -> (
        modifies1 c1 h0 h1
        /\ Seq.equal (as_seq h1 c1) c1_s
      )
      | _ -> False
  )

val decrypt_ciphertext1:
  #kcs: supportedKemCipherSuite
  -> c1: c1_buff kcs
  -> th1: hash_out_buff kcs
  -> prk1e: hash_out_buff kcs
  -> ptx1_buffer: plaintext1_buff
  -> ST.Stack c_response
  (requires fun h0 ->
    live h0 c1 /\ live h0 th1 /\ live h0 prk1e /\ live h0 ptx1_buffer
    /\ B.all_disjoint [loc c1; loc th1; loc prk1e; loc ptx1_buffer]
  )
  (ensures fun h0 res h1 ->
    let ptx1_s_opt = Spec.decrypt_ciphertext1 #kcs (as_seq h0 c1) (as_seq h0 th1) (as_seq h0 prk1e) in

    (match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CDecryptionFailure -> modifies1 ptx1_buffer h0 h1
      | TypeEdhoc.CSuccess -> (
        match ptx1_s_opt with
          | None -> False
          | Some ptx1_s ->
            modifies1 ptx1_buffer h0 h1
            /\ Seq.equal (as_seq h1 ptx1_buffer) ptx1_s
      )
      | _ -> False
    )
  )

/// -------------
/// Ciphertext 2
/// -------------
val encrypt_plaintext2:
  #kcs: supportedKemCipherSuite
  -> ptx2: plaintext2 kcs
  -> th2: hash_out_buff kcs
  -> prk2e: hash_out_buff kcs
  -> c2: c2_buff kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_plaintext2 h0 ptx2 /\ live h0 th2 /\ live h0 prk2e /\ live h0 c2
    /\ B.all_disjoint [plaintext2_union ptx2; loc th2; loc prk2e; loc c2]
  )
  (ensures fun h0 res h1 ->
    let c2_s = Spec.encrypt_plaintext2 #kcs (plaintext2_eval h0 ptx2) (as_seq h0 th2) (as_seq h0 prk2e) in

    match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CSuccess -> (
        modifies1 c2 h0 h1
        /\ Seq.equal (as_seq h1 c2) c2_s
      )
      | _ -> False
  )

val decrypt_ciphertext2:
  #kcs: supportedKemCipherSuite
  -> c2: c2_buff kcs
  -> th2: hash_out_buff kcs
  -> prk2e: hash_out_buff kcs
  -> p2_buffer: plaintext2_buff kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    live h0 c2 /\ live h0 th2 /\ live h0 prk2e /\ live h0 p2_buffer
    /\ B.all_disjoint [loc c2; loc th2; loc prk2e; loc p2_buffer]
  )
  (ensures fun h0 res h1 ->
    let p2_s_opt = Spec.decrypt_ciphertext2 #kcs (as_seq h0 c2) (as_seq h0 th2) (as_seq h0 prk2e) in

    (match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CDecryptionFailure -> modifies1 p2_buffer h0 h1
      | TypeEdhoc.CSuccess -> (
        match p2_s_opt with
          | None -> False
          | Some p2_s ->
            modifies1 p2_buffer h0 h1
            /\ Seq.equal (as_seq h1 p2_buffer) p2_s
      )
      | _ -> False
    )
  )

/// -------------
/// Ciphertext 3
/// -------------
val encrypt_plaintext3:
  #kcs: supportedKemCipherSuite
  -> ptx3: plaintext3 kcs
  -> th3: hash_out_buff kcs
  -> prk3e2m: hash_out_buff kcs
  -> c3: c3_buff kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    is_valid_plaintext3 h0 ptx3 /\ live h0 th3 /\ live h0 prk3e2m /\ live h0 c3
    /\ B.all_disjoint [plaintext3_union ptx3; loc th3; loc prk3e2m; loc c3]
  )
  (ensures fun h0 res h1 ->
    let c3_s = Spec.encrypt_plaintext3 #kcs (plaintext3_eval h0 ptx3) (as_seq h0 th3) (as_seq h0 prk3e2m) in

    match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CSuccess -> (
        modifies1 c3 h0 h1
        /\ Seq.equal (as_seq h1 c3) c3_s
      )
      | _ -> False
  )

val decrypt_ciphertext3:
  #kcs: supportedKemCipherSuite
  -> c3: c3_buff kcs
  -> th3: hash_out_buff kcs
  -> prk3e2m: hash_out_buff kcs
  -> p3_buffer: plaintext3_buff kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    live h0 c3 /\ live h0 th3 /\ live h0 prk3e2m /\ live h0 p3_buffer
    /\ B.all_disjoint [loc c3; loc th3; loc prk3e2m; loc p3_buffer]
  )
  (ensures fun h0 res h1 ->
    let p3_s_opt = Spec.decrypt_ciphertext3 #kcs (as_seq h0 c3) (as_seq h0 th3) (as_seq h0 prk3e2m) in

    (match res with
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
      | TypeEdhoc.CDecryptionFailure -> modifies1 p3_buffer h0 h1
      | TypeEdhoc.CSuccess -> (
        match p3_s_opt with
          | None -> False
          | Some p3_s ->
            modifies1 p3_buffer h0 h1
            /\ Seq.equal (as_seq h1 p3_buffer) p3_s
      )
      | _ -> False
    )
  )