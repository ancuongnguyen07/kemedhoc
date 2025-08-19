(*
I build a customized encoding/deconding mechanism here
to leverage the simplicity of high-level FStar model.
Actually, EDHOC uses CBOR under the hood, but there is no
published verified CBOR model at this moment (EverParse is
working on it, found a CBOR-specific branch in EverParse repo,
but it seems way long to be released.)

Several functions here are ported from libsignal
(https://github.com/Inria-Prosecco/libsignal-protocol-wasm-fstar/tree/master)
*)

module Spec.EDHOC.Serialization

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

module FBytes = FStar.Bytes
module Crypto = Spec.EDHOC.CryptoPrimitives
module Seq = Lib.Sequence

open Spec.EDHOC.CommonPred
open Spec.EDHOC.Base.Definitions

// Utility constants
inline_for_extraction
let offset:size_nat = 2
inline_for_extraction
let max_nof_bytes_nat = 4 // to fit size_nat
inline_for_extraction
let size128 : size_nat =  128
inline_for_extraction
let size16384 : size_nat = 16384
inline_for_extraction
let size2097152 : size_nat = 2097152
inline_for_extraction
let size268435456 : size_nat =  268435456

// the below value defines the number of bytes representing
// the byte len at the beginning of each serialized bytes
// let fixed_max_size_byte:nat = 5
// let one_byte_threshold = 0x7ful
// let two_byte_threshold = 0x3ffful
// let three_byte_threshold = 0x1ffffful
// let four_byte_threshold = 0xffffffful
// greater than `four_byte_threshold` is 5 byte long

inline_for_extraction
type serializable_bytes = b:bytes{length b <= size16384}

val ( @< ):
  #len1:size_nat
  -> #len2:size_nat{len1 + len2 <= max_size_t}
  -> a:lbytes len1
  -> b:lbytes len2
  -> c:lbytes (len1 + len2)

val lemma_concat_alias_equiv:
  #len1:size_nat
  -> #len2:size_nat{len1 + len2 <= max_size_t}
  -> a:lbytes len1
  -> b:lbytes len2
  -> Lemma (ensures a @< b == concat a b)
  [SMTPat (a @< b)]

/// concat2 and concat3 are already available at `Lib.Buffer` in HACL
/// I need to implement concat4 and concat5 for EDHOC.

/// Firstly I need to introduce high-level lemmas for concat4 and concat5
val lemma_concat4:
  #a:Type0
  -> len1:size_nat
  -> s1:Seq.lseq a len1
  -> len2:size_nat{len1 + len2 <= max_size_t}
  -> s2:Seq.lseq a len2
  -> len3:size_nat{len1 + len2 + len3 <= max_size_t}
  -> s3:Seq.lseq a len3
  -> len4:size_nat{len1 + len2 + len3 + len4 <= max_size_t}
  -> s4:Seq.lseq a len4
  -> s:Seq.lseq a (len1 + len2 + len3 + len4)
  -> Lemma (requires Seq.sub s 0 len1 == s1
            /\ Seq.sub s len1 len2 == s2
            /\ Seq.sub s (len1 + len2) len3 == s3
            /\ Seq.sub s (len1 + len2 + len3) len4 == s4)
  (ensures s == Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4)

val lemma_concat5:
  #a:Type0
  -> len1:size_nat
  -> s1:Seq.lseq a len1
  -> len2:size_nat{len1 + len2 <= max_size_t}
  -> s2:Seq.lseq a len2
  -> len3:size_nat{len1 + len2 + len3 <= max_size_t}
  -> s3:Seq.lseq a len3
  -> len4:size_nat{len1 + len2 + len3 + len4 <= max_size_t}
  -> s4:Seq.lseq a len4
  -> len5:size_nat{len1 + len2 + len3 + len4 + len5 <= max_size_t}
  -> s5:Seq.lseq a len5
  -> s:Seq.lseq a (len1 + len2 + len3 + len4 + len5)
  -> Lemma (requires Seq.sub s 0 len1 == s1
                /\ Seq.sub s len1 len2 == s2
                /\ Seq.sub s (len1 + len2) len3 == s3
                /\ Seq.sub s (len1 + len2 + len3) len4 == s4
                /\ Seq.sub s (len1 + len2 + len3 + len4) len5 == s5)
  (ensures s == Seq.concat (Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4) s5)

val concat4:
  #len1:size_nat
  -> #len2:size_nat{len1 + len2 <= max_size_t}
  -> #len3:size_nat{len1 + len2 + len3 <= max_size_t}
  -> #len4:size_nat{len1 + len2 + len3 + len4 <= max_size_t}
  -> s1:lbytes len1
  -> s2:lbytes len2
  -> s3:lbytes len3
  -> s4:lbytes len4
  -> s:lbytes (len1 + len2 + len3 + len4)

val lemma_concat4_comp:
  #len1:size_nat
  -> #len2:size_nat{len1 + len2 <= max_size_t}
  -> #len3:size_nat{len1 + len2 + len3 <= max_size_t}
  -> #len4:size_nat{len1 + len2 + len3 + len4 <= max_size_t}
  -> s1:lbytes len1
  -> s2:lbytes len2
  -> s3:lbytes len3
  -> s4:lbytes len4
  -> Lemma (ensures (
    let s = concat4 s1 s2 s3 s4 in
    Seq.equal s1 (Seq.sub s 0 len1)
    /\ Seq.equal s2 (Seq.sub s len1 len2)
    /\ Seq.equal s3 (Seq.sub s (len1 + len2) len3)
    /\ Seq.equal s4 (Seq.sub s (len1 + len2 + len3) len4)
    /\ s == Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4
  ))
  [SMTPat (concat4 #len1 #len2 #len3 #len4 s1 s2 s3 s4)]


val concat5:
  #len1:size_nat
  -> #len2:size_nat{len1 + len2 <= max_size_t}
  -> #len3:size_nat{len1 + len2 + len3 <= max_size_t}
  -> #len4:size_nat{len1 + len2 + len3 + len4 <= max_size_t}
  -> #len5:size_nat{len1 + len2 + len3 + len4 + len5 <= max_size_t}
  -> s1:lbytes len1
  -> s2:lbytes len2
  -> s3:lbytes len3
  -> s4:lbytes len4
  -> s5:lbytes len5
  -> s:lbytes (len1 + len2 + len3 + len4 + len5)


val lemma_concat5_comp:
  #len1:size_nat
  -> #len2:size_nat{len1 + len2 <= max_size_t}
  -> #len3:size_nat{len1 + len2 + len3 <= max_size_t}
  -> #len4:size_nat{len1 + len2 + len3 + len4 <= max_size_t}
  -> #len5:size_nat{len1 + len2 + len3 + len4 + len5 <= max_size_t}
  -> s1:lbytes len1
  -> s2:lbytes len2
  -> s3:lbytes len3
  -> s4:lbytes len4
  -> s5:lbytes len5
  -> Lemma (ensures (
    let s = concat5 s1 s2 s3 s4 s5 in
    Seq.equal s1 (Seq.sub s 0 len1)
    /\ Seq.equal s2 (Seq.sub s len1 len2)
    /\ Seq.equal s3 (Seq.sub s (len1 + len2) len3)
    /\ Seq.equal s4 (Seq.sub s (len1 + len2 + len3) len4)
    /\ Seq.equal s5 (Seq.sub s (len1 + len2 + len3 + len4) len5)
    /\ s == Seq.concat (Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4) s5
  ))
  [SMTPat (concat5 s1 s2 s3 s4 s5)]

let concat_lbytes:
  #len1:size_nat
  -> #len2:size_nat{len1 + len2 <= max_size_t}
  -> a:lbytes len1
  -> b:lbytes len2
  -> c:lbytes (len1 + len2)
  = fun #len1 #len2 a b -> a @< b

val ( @: ):
  #len:size_nat{len + offset <= max_size_t}
  -> a:nat{a < pow2 (8 * offset)}
  -> b:lbytes len
  -> lbytes (len + offset)

// val nat_to_bytes:
//   n:inbound_size_nat
//   -> Tot (r:lbytes (FBytes.repr_bytes n))

/// `n < pow2 (8 * (FByts.repr_bytes n))` guarantees that the natural
/// number `n` does not greater than the supposed byte space is able
/// to represent.
let nat_to_bytes (n:inbound_size_nat)
  : Tot (r:lbytes (FBytes.repr_bytes n))
  = 
  // `bytes_of_int` return lbytes of FStar
  // not lbytes from HACL*
  nat_to_bytes_le #SEC (FBytes.repr_bytes n) n

let bytes_to_nat (b:bytes{length b <= max_nof_bytes_nat})
  :inbound_size_nat
  = nat_from_bytes_le #SEC b

let lemma_nat_to_bytes_to_nat
  (n:inbound_size_nat)
  : Lemma (ensures n == bytes_to_nat (nat_to_bytes n))
  [SMTPat (nat_to_bytes n)]
  = ()

let lemma_bytes_to_nat_to_bytes
  (b:bytes{length b <= max_nof_bytes_nat})
  : Lemma
  (ensures ( 
    let b' = nat_to_bytes (bytes_to_nat b) in
    b == b'
  ))
  [SMTPat (bytes_to_nat b)]
  = 
  // lemma_nat_from_to_bytes_le_preserves_value #SEC b n_n
  admit ()

/// Natural numbers Serialization/Deserialization
inline_for_extraction
val serialize_nat_to_bytes_get_length:
  n:size_nat
  -> Tot (r:size_nat{r <= max_nof_bytes_nat + offset})
val serialize_nat_to_bytes:
  n:size_nat
  -> lbytes (FBytes.repr_bytes n + offset)

// Return the deserialized Nat and the amount of
// deseralized bytes.
val deserialize_bytes_to_nat:
  b:serializable_bytes{length b > offset}
  -> eresult (inbound_nat & pos_size_nat)

// /// Lbytes Serialization/Deserialization
inline_for_extraction
val serialize_lbytes_get_length:
  #len:size_nat{len <= size16384}
  -> lb:lbytes len
  -> Tot (r:size_nat{r = len + offset})
val serialize_lbytes:
  #len:size_nat{len < size16384}
  -> lb:lbytes len
  -> lbytes (len + offset)

// /// Bytes Serialization/Deserialization
inline_for_extraction
val serialize_bytes_get_length:
  b:serializable_bytes
  -> Tot (r:size_nat{r = length b + offset})
val serialize_bytes:
  b:serializable_bytes
  -> lbytes (length b + offset)

// // Return the deserialized bytes and the amount of
// // deserialized bytes.
val deserialize_bytes:
  b:serializable_bytes
  -> max_payload_size:size_nat
  -> start:size_nat{start + offset < length b}
  -> eresult (bytes & size_nat)
