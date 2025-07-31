module Spec.EDHOC.Base.Definitions

open FStar.Mul

(*HACL libs*)
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

// #set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

type error =
  (*EDHOC standardized errors*)
  | UnspecifiedError
  | UnsupportedCipherSuite
  | UnknownCredentialID
  (*Implementation-specific errors*)
  | MissingKey
  | InputSize // too long or too short input
  | DecryptionFailed
  | UnsupportedAuthenticationMethod
  | InvalidECPoint
  | SerializationDeserializationFailed
  | SigningFailed
  | IntegrityCheckFailed
  | InvalidState
  | InvalidCredential

let to_error_code (e: error): nat
  = match e with
    | UnspecifiedError -> 1
    | UnsupportedCipherSuite -> 2
    | UnknownCredentialID -> 3
    | MissingKey -> 4
    | InputSize -> 5
    | DecryptionFailed -> 6
    | UnsupportedAuthenticationMethod -> 7
    | InvalidECPoint -> 8
    | SerializationDeserializationFailed -> 9
    | SigningFailed -> 10
    | IntegrityCheckFailed -> 11
    | InvalidState -> 12
    | InvalidCredential -> 13

type result (a b:Type) =
  | Res : v:a -> result a b
  | Fail: v:b -> result a b

let eresult (a:Type) = result a error

type method_enum =
  | SigSig
  | SigStat
  | StatSig
  | StatStat

type party_enum =
  | Initiator
  | Responder

type method_label = n:nat{n > 0 /\ n <= 4}
val method_as_nat:
  method_enum
  -> Tot method_label

val label_to_method:
  method_label
  -> Tot method_enum

let lemma_method_as_nat_to_method_equiv
  (m:method_enum)
  : Lemma (ensures m == label_to_method (method_as_nat m))
  [SMTPat (method_as_nat m)]
  = ()

let lemma_label_to_method_label_equiv
  (l:method_label)
  : Lemma (ensures l = method_as_nat (label_to_method l))
  [SMTPat (label_to_method l)]
  = ()