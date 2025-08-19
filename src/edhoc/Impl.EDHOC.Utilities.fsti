module Impl.EDHOC.Utilities

module FBytes = FStar.Bytes

open FStar.Mul

(*HACL modules*)
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntTypes
open Lib.RawIntTypes

open LowStar.BufferOps

(*LowStar modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence
module ByteSeq = Lib.ByteSequence


open Spec.EDHOC.CommonPred
module SpecSerd = Spec.EDHOC.Serialization

/// -----------------------
/// Convenient buffer types
/// -----------------------

inline_for_extraction
type serializable_buff = b:buffer_t MUT uint8{length b <= SpecSerd.size16384}

/// The `as_seq` version for variant-length buffers
inline_for_extraction
let as_seq_buff (#ty:buftype) (#a:Type0)
  (h:HS.mem) (b:buffer_t ty a)
  = as_seq #ty #a #(size (length b)) h b

inline_for_extraction noextract
let null (#ty:buftype) (#a:Type0)
  :buffer_t ty a
  = match ty with
    | IMMUT -> LowStar.ImmutableBuffer.inull #a
    | MUT -> LowStar.Buffer.null #a
    | CONST -> LowStar.ConstBuffer.of_buffer (LowStar.Buffer.null #a)

// Ghost is_null
let g_is_null (#ty:buftype) (#a:Type0) (b:buffer_t ty a)
  :GTot bool
  = match ty with
    | IMMUT -> LowStar.Buffer.g_is_null #a #(LowStar.ImmutableBuffer.immutable_preorder a)
                                          #(LowStar.ImmutableBuffer.immutable_preorder a)
                                          b
    | MUT -> LowStar.Buffer.g_is_null #a #(LowStar.Buffer.trivial_preorder a)
                                          #(LowStar.Buffer.trivial_preorder a)
                                          b
    | CONST -> LowStar.Buffer.g_is_null #a (LowStar.ConstBuffer.as_mbuf b)

inline_for_extraction noextract
let is_null (#ty:buftype) (#a:Type0) (b:buffer_t ty a)
  :ST.Stack bool
  (requires fun h0 -> live h0 b)
  (ensures fun h0 res h1 -> h0 == h1 /\ res == g_is_null b)
  = match ty with
    | IMMUT -> LowStar.Buffer.is_null #a #(LowStar.ImmutableBuffer.immutable_preorder a)
                                          #(LowStar.ImmutableBuffer.immutable_preorder a)
                                          b
    | MUT -> LowStar.Buffer.is_null #a #(LowStar.Buffer.trivial_preorder a)
                                          #(LowStar.Buffer.trivial_preorder a)
                                          b
    | CONST -> LowStar.Buffer.is_null #a (LowStar.ConstBuffer.cast b)


unfold let lbuffer_t_or_null (ty:buftype) (a:Type0) (len:size_t)
  = b:buffer_t ty a {~(g_is_null b) ==> length #ty #a b == size_v len}
unfold let buffer_t_or_null_max_len (ty:buftype) (a:Type0) (max_len:size_t)
  = b:buffer_t ty a {~(g_is_null b) ==> length #ty #a b <= size_v max_len}

type lbuffer_or_null = lbuffer_t_or_null MUT

let unchanged_lbuffer_or_null (#a:Type0) (#len:size_t) (h0 h1:HS.mem)
  (b:lbuffer_or_null a len)
  = if g_is_null b then True
  else (
    let b':lbuffer a len = b in
    Seq.equal (as_seq h1 b') (as_seq h0 b')
  )

// Alias for `as_seq` for a non-null buffer
// let nn_as_seq (#t:buftype) (#a:Type0) (#len:size_t)
//   (h:HS.mem) (b:lbuffer_t_or_null t a len)
//   : Ghost (S.lseq a (size_v len))
//   (requires (not (g_is_null b)))
//   (ensures fun _ -> True) // trivial post-condition
//   = let b':lbuffer_t t a len = b in
//   as_seq h b'

/// lbuffer_or_null to sequence
let lbuffer_or_null_as_seq (#t:buftype) (#a:Type0) (#len:size_t)
  (h:HS.mem) (lb:lbuffer_t_or_null t a len)
  :GTot (option (Seq.lseq a (size_v len)))
  = if g_is_null lb then None else Some (as_seq h (lb <: lbuffer_t t a len))

/// convert lbuffer_or_null to not-null-known sequence
let lbuffer_or_null_as_not_null (#t:buftype) (#a:Type0) (#len:size_t)
  (lb:lbuffer_t_or_null t a len)
  :Ghost (lbuffer_t t a len)
  (requires ~(g_is_null lb)) (ensures (fun _ -> True))
  = lb

/// convert not-null-known lbuffer to sequence
let nn_as_seq (#t:buftype) (#a:Type0) (#len:size_t)
  (h:HS.mem) (lb:lbuffer_t_or_null t a len)
  :Ghost (Seq.lseq a (size_v len))
  (requires (not (g_is_null lb))) (ensures (fun _ -> True))
  = as_seq h (lb <: lbuffer_t t a len)

/// update function for lbuffer_or_null
let update_lbuffer_or_null (#t:buftype) (#a:Type0) (#len:size_t)
  (h:HS.mem) (dst:lbuffer_or_null a len)
  (start:size_t) (n:size_t{size_v n + size_v start <= size_v len})
  (src:lbuffer_t_or_null t a n)
  : ST.Stack unit
  (requires fun h0 ->
    live h0 dst /\ live h0 src /\ disjoint src dst
    /\ (g_is_null src <==> g_is_null dst)
  )
  (ensures fun h0 _ h1 -> (
    if (g_is_null src) then modifies0 h0 h1
    else (
      modifies (loc (lbuffer_or_null_as_not_null dst)) h0 h1
      /\ Seq.equal (nn_as_seq h1 dst)
        (Seq.update_sub (nn_as_seq h0 dst) (size_v start) (size_v n) (nn_as_seq h0 src))
    )
  ))
  = if is_null src then ()
  else update_sub #t #a #len (dst <: (lbuffer a len)) start n
    (src <: lbuffer_t t a n)

/// ---------------------------
/// Lemmas for lbuffer and its corresponding nat
/// ---------------------------

let lemma_lbuffer_1ul_to_nat_equiv (h:HS.mem)
  (buf:lbuffer uint8 1ul)
  : Lemma (ensures (
    let buffer_nat = uint_to_nat (bget h buf 0) in
    let spec_nat = SpecSerd.bytes_to_nat (as_seq h buf) in
    let spec_bytes = SpecSerd.nat_to_bytes spec_nat in

    buffer_nat = spec_nat
    /\ Seq.equal spec_bytes (as_seq h buf)
  ))
  [SMTPat (uint_to_nat (bget h buf 0))]
  = let buffer_nat = uint_to_nat (bget h buf 0) in
  let spec_nat = SpecSerd.bytes_to_nat (as_seq h buf) in
  let spec_bytes = SpecSerd.nat_to_bytes spec_nat in
  assert(Seq.length spec_bytes = length buf);
  admit()

/// ---------------------------
/// Lemmas for `modifies` clauses
/// ---------------------------
// let lemma_modifies1_modifes_equiv ()

/// ---------------------------
/// Concat functions and lemmas
/// ---------------------------

val concat_buff2:
  #t:buftype
  -> #a:Type0
  -> #len1:size_t
  -> #len2:size_t{size_v len1 + size_v len2 <= max_size_t}
  -> buff1:lbuffer_t t a len1
  -> buff2:lbuffer_t t a len2
  -> output:lbuffer a (len1 +! len2)
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 buff1 /\ live h0 buff2 /\ live h0 output
    /\ disjoint output buff1 /\ disjoint output buff2
  ))
  (ensures fun h0 _ h1 -> (
    modifies1 output h0 h1
    /\ (as_seq h1 output) == (Seq.concat (as_seq h0 buff1) (as_seq h0 buff2))
  ))

val concat_buff3:
  #t:buftype
  -> #a:Type0
  -> #len1:size_t
  -> #len2:size_t{size_v len1 + size_v len2 <= max_size_t}
  -> #len3:size_t{size_v len1 + size_v len2 + size_v len3 <= max_size_t}
  -> buff1:lbuffer_t t a len1
  -> buff2:lbuffer_t t a len2
  -> buff3:lbuffer_t t a len3
  -> output:lbuffer a (len1 +! len2 +! len3)
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 buff1 /\ live h0 buff2 /\ live h0 buff3 /\ live h0 output
    /\ disjoint output buff1 /\ disjoint output buff2 /\ disjoint output buff3
  ))
  (ensures fun h0 _ h1 -> (
    modifies1 output h0 h1
    /\ (as_seq h1 output) == Seq.concat (Seq.concat (as_seq h0 buff1) (as_seq h0 buff2)) (as_seq h0 buff3)
  ))

/// Now is the low-level concat4 and concat5
val concat_buff4:
  #t:buftype
  -> #a:Type0
  -> #len1:size_t
  -> #len2:size_t{size_v len1 + size_v len2 <= max_size_t}
  -> #len3:size_t{size_v len1 + size_v len2 + size_v len3 <= max_size_t}
  -> #len4:size_t{size_v len1 + size_v len2 + size_v len3 + size_v len4 <= max_size_t}
  -> buff1:lbuffer_t t a len1
  -> buff2:lbuffer_t t a len2
  -> buff3:lbuffer_t t a len3
  -> buff4:lbuffer_t t a len4
  -> output:lbuffer a (len1 +! len2 +! len3 +! len4)
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 buff1 /\ live h0 buff2 /\ live h0 buff3 /\ live h0 buff4
    /\ live h0 output /\ disjoint output buff1 /\ disjoint output buff2
    /\ disjoint output buff3 /\ disjoint output buff4
  )
  (requires fun h0 _ h1 ->
    modifies1 output h0 h1
    /\ (as_seq h1 output) == (Seq.concat (Seq.concat (Seq.concat (as_seq h0 buff1) (as_seq h0 buff2)) (as_seq h0 buff3)) (as_seq h0 buff4))
  )
  
val concat_buff5:
  #t:buftype
  -> #a:Type0
  -> #len1:size_t
  -> #len2:size_t{size_v len1 + size_v len2 <= max_size_t}
  -> #len3:size_t{size_v len1 + size_v len2 + size_v len3 <= max_size_t}
  -> #len4:size_t{size_v len1 + size_v len2 + size_v len3 + size_v len4 <= max_size_t}
  -> #len5:size_t{size_v len1 + size_v len2 + size_v len3 + size_v len4 + size_v len5 <= max_size_t}
  -> buff1:lbuffer_t t a len1
  -> buff2:lbuffer_t t a len2
  -> buff3:lbuffer_t t a len3
  -> buff4:lbuffer_t t a len4
  -> buff5:lbuffer_t t a len5
  -> output:lbuffer a (len1 +! len2 +! len3 +! len4 +! len5)
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 buff1 /\ live h0 buff2 /\ live h0 buff3 /\ live h0 buff4
    /\ live h0 buff5 /\ live h0 output
    /\ disjoint output buff1 /\ disjoint output buff2
    /\ disjoint output buff3 /\ disjoint output buff4 /\ disjoint output buff5 
  )
  (ensures fun h0 _ h1 ->
    modifies1 output h0 h1
    /\ (as_seq h1 output) == (Seq.concat (Seq.concat (Seq.concat (Seq.concat (as_seq h0 buff1) (as_seq h0 buff2)) (as_seq h0 buff3)) (as_seq h0 buff4)) (as_seq h0 buff5))
  )


inline_for_extraction
val split_buffer:
  #a:Type0
  -> #len:size_t
  -> s:lbuffer a len
  -> pos:size_t{v pos < v len}
  -> ST.Stack ((lbuffer a pos) & (lbuffer a (size (v len - v pos))))
  (requires fun h0 -> live h0 s)
  (ensures fun h0 (s1,s2) h1 -> modifies0 h0 h1
    /\ live h1 s1 /\ live h1 s2
    /\ as_seq h0 s == as_seq h1 s
    /\ as_seq h1 s1 == Seq.sub (as_seq h0 s) 0 (v pos)
    /\ as_seq h1 s2 == Seq.sub (as_seq h0 s) (v pos) (v len - v pos)
    /\ as_seq h1 s == (Seq.concat (as_seq h1 s1) (as_seq h1 s2))
  )

val nat_to_bytes:
  len:size_t{size_v len <= 2 /\ size_v len > 0}
  -> buff:lbuffer uint8 len
  -> n:nat{n < pow2 (bits U8 * (size_v len))}
  -> ST.Stack unit
  (requires fun h0 ->
            live h0 buff /\ size_v len = FBytes.repr_bytes n
  )
  (ensures fun h0 _ h1 -> modifies1 buff h0 h1
    /\ as_seq h1 buff == SpecSerd.nat_to_bytes n
  )
  (decreases len)