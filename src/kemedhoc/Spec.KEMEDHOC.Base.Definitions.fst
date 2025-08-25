module Spec.KEMEDHOC.Base.Definitions

type error =
  (*EDHOC standardized errors*)
  | UnspecifiedError
  | UnsupportedCipherSuite
  | UnknownCredentialID
  // Implementation-specific errors
  | InvalidState
  | InvalidCredential
  | DecryptionFailed
  | IntegrityCheckFailed

let error_to_code (e: error): nat
  = match e with
    | UnspecifiedError -> 1
    | UnsupportedCipherSuite -> 2
    | UnknownCredentialID -> 3
    | InvalidState -> 4
    | InvalidCredential -> 5
    | DecryptionFailed -> 6
    | IntegrityCheckFailed -> 7

type result (a b:Type) =
  | Res : v:a -> result a b
  | Fail: v:b -> result a b

let eresult (a:Type) = result a error

type method_enum =
  | KemKem

let method_enum_to_nat (m: method_enum): nat
  = match m with
    | KemKem -> 5 // 1-4 for EDHOC methods, 5 for KEMEDHOC

inline_for_extraction
type method_label = n:nat{n = 5}

let nat_to_method (n: method_label): method_enum
  = match n with
    | 5 -> KemKem

let lemma_method_to_nat_correctness (m: method_enum)
  : Lemma (ensures (
    let label = method_enum_to_nat m in
    nat_to_method label == m
  ))
  [SMTPat (method_enum_to_nat m)]
  = ()

let lemma_nat_to_method_correctness (label: method_label)
  : Lemma (ensures (
    let m = nat_to_method label in
    method_enum_to_nat m == label
  ))
  [SMTPat (nat_to_method label)]
  = ()