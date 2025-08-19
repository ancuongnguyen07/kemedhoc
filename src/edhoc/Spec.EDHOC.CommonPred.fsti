module Spec.EDHOC.CommonPred

module FBytes = FStar.Bytes

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

inline_for_extraction
type pos_size_nat = s:size_nat{s > 0}
inline_for_extraction
type inbound_size_nat = s:size_nat{s < pow2 (8*FBytes.repr_bytes s)}
inline_for_extraction
type inbound_nat = n:nat{n < pow2 (8*FBytes.repr_bytes n)}

let single_byte_nat = n:size_nat{n < 256}

val bytes_less_than_equal_max:
  bytes
  -> bool

val bytes_less_than_equal_max_offset:
  bytes
  -> nat
  -> bool

val not_empty_bytes:
  bytes
  -> bool

val in_scope_byte:
  bytes
  -> bool

val option_bytes_less_than_equal_max:
  option bytes
  -> bool

val option_length_lbyte:
  #len:size_nat
  -> option (lbytes len)
  -> size_nat

val bytes_eq:
  b1:bytes{bytes_less_than_equal_max b1}
  -> b2:bytes{bytes_less_than_equal_max b2}
  -> res:bool{ if (length b1 <> length b2) then not res
                else res <==> b1 == b2}

val unequal_lbytes_eq:
  #len1:size_nat
  -> #len2:size_nat
  -> b1:lbytes len1
  -> b2:lbytes len2
  -> res:bool{res <==> (len1 = len2 /\ b1 == b2)}

/// Wrapper of a Option value that is ensured as Some
val must:
  #a:Type
  -> x:option a {Option.isSome x}
  -> Tot a

// convert propositional equality to decidable equality
// let eqb_from_prop (#a:Type) (x y:a)
//   :bool
//   = if (x == y) then true else false