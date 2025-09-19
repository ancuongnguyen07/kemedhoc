module Impl.KEMEDHOC.Core.Utilities

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

open Impl.KEMEDHOC.Types

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

module SpecParser = Spec.KEMEDHOC.Parser
module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module TypeEdhoc = TypeHelper.EDHOC


open Impl.KEMEDHOC.CryptoPrimitives
open Impl.KEMEDHOC.Types
open Impl.KEMEDHOC.Parser
open Spec.KEMEDHOC.Base.Definitions


open LowStar.BufferOps

/// Check Credential
val check_credential:
  cred_A: id_cred_buffer
  -> cred_B: id_cred_buffer
  -> ST.Stack c_response
  (requires fun h0 ->
    live h0 cred_A /\ live h0 cred_B
  )
  (ensures fun h0 res h1 -> (res == TypeEdhoc.CSuccess \/ res == TypeEdhoc.CInvalidCredential)
    /\ modifies0 h0 h1
    /\ (match res with
      | TypeEdhoc.CSuccess -> (
        (Seq.equal (as_seq h0 cred_A) (as_seq h0 cred_B))
      )
      | TypeEdhoc.CInvalidCredential ->
        ~(Seq.equal (as_seq h0 cred_A) (as_seq h0 cred_B))
      | _ -> False
    )
  )

let check_credential cred_A cred_B
  = if (lbytes_eq cred_A cred_B) then TypeEdhoc.CSuccess
  else TypeEdhoc.CInvalidCredential

/// Check MAC
val check_mac:
  #kcs: supportedKemCipherSuite
  -> mac_A: mac23_buff kcs
  -> mac_B: mac23_buff kcs
  -> ST.Stack c_response
  (requires fun h0 ->
    live h0 mac_A /\ live h0 mac_B
  )
  (ensures fun h0 res h1 ->
    let res_s = Seq.equal (as_seq h0 mac_A) (as_seq h0 mac_B) in

    modifies0 h0 h1
    /\ (match res with
      | TypeEdhoc.CSuccess -> res_s
      | TypeEdhoc.CIntegrityCheckFailed -> ~res_s
      | _ -> False
    )
  )

let check_mac #kcs mac_A mac_B
  = if (lbytes_eq mac_A mac_B) then TypeEdhoc.CSuccess
  else TypeEdhoc.CIntegrityCheckFailed