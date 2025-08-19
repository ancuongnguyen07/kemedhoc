module Spec.EDHOC.CommonPred

module FBytes = FStar.Bytes

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


// Predicated Type

let bytes_less_than_equal_max b
  = length b <= max_size_t

let bytes_less_than_equal_max_offset b offset
  = length b + offset <= max_size_t

let not_empty_bytes b
  = length b > 0

// Check if the given byte is not empty and not greater the MAX
let in_scope_byte b
  = not_empty_bytes b && bytes_less_than_equal_max b

let option_bytes_less_than_equal_max op
  = match op with
    | None -> true
    | Some b -> bytes_less_than_equal_max b

let option_length_lbyte #len o
  = match o with
    | None -> 0
    | Some _ -> len

let bytes_eq b1 b2
  = if (length b1 <> length b2) then false
  else (
    let b1_lbytes:lbytes (length b1) = b1 in
    let b2_lbytes:lbytes (length b2) = b2 in
    lbytes_eq b1_lbytes b2_lbytes
  )

let unequal_lbytes_eq #len1 #len2 b1 b2
  = if (len1 <> len2) then false
  else lbytes_eq #len1 b1 b2

let must x = match x with
              | Some v -> v
