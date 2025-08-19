module Impl.EDHOC.Utilities

(*HACL modules*)
module LibBuf = Lib.Buffer


(*LowStar modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence
module SerdSpec = Spec.EDHOC.Serialization
module FSeq = FStar.Seq
module FSeqProp = FStar.Seq.Properties

/// ---------------------------
/// Concat functions and lemmas
/// ---------------------------

let concat_buff2 #t #a #len1 #len2 buff1 buff2 output
  = let h0 = ST.get () in
  update_sub output (size 0) len1 buff1;
  let h1 = ST.get () in
  update_sub output len1 len2 buff2;
  let h2 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h1 output) 0 (size_v len1)) (as_seq h0 buff1);
  (**) Seq.eq_intro (Seq.sub (as_seq h2 output) 0 (size_v len1)) (as_seq h0 buff1);
  (**) Seq.eq_intro (Seq.sub (as_seq h2 output) (size_v len1) (size_v len2)) (as_seq h0 buff2);
  (**) Seq.lemma_concat2 (size_v len1) (as_seq h0 buff1) (size_v len2) (as_seq h0 buff2) (as_seq h2 output);
  ()

let concat_buff3 #t #a #len1 #len2 #len3 buff1 buff2 buff3 output
  = let h0 = ST.get () in
  update_sub output (size 0) len1 buff1;
  update_sub output len1 len2 buff2;
  let h1 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h1 output) 0 (size_v len1)) (as_seq h0 buff1);

  update_sub output (len1 +! len2) len3 buff3;
  let h2 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h2 output) 0 (size_v len1)) (as_seq h0 buff1);
  (**) Seq.eq_intro (Seq.sub (as_seq h2 output) (size_v len1) (size_v len2)) (as_seq h0 buff2);
  (**) Seq.lemma_concat3 (size_v len1) (as_seq h0 buff1) (size_v len2) (as_seq h0 buff2)
                      (size_v len3) (as_seq h0 buff3) (as_seq h2 output)

let concat_buff4 #t #a #len1 #len2 #len3 #len4 buff1 buff2 buff3 buff4 output
  = let h0 = ST.get () in
  update_sub output (size 0) len1 buff1;
  update_sub output len1 len2 buff2;
  let h1 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h1 output) 0 (size_v len1)) (as_seq h0 buff1);
  
  update_sub output (len1 +! len2) len3 buff3;
  let h2 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h2 output) 0 (size_v len1)) (as_seq h0 buff1);
  (**) Seq.eq_intro (Seq.sub (as_seq h2 output) (size_v len1) (size_v len2)) (as_seq h0 buff2);
  
  update_sub output (len1 +! len2 +! len3) len4 buff4;
  let h3 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h3 output) 0 (size_v len1)) (as_seq h0 buff1);
  (**) Seq.eq_intro (Seq.sub (as_seq h3 output) (size_v len1) (size_v len2)) (as_seq h0 buff2);
  (**) Seq.eq_intro (Seq.sub (as_seq h3 output) (size_v len1 + size_v len2) (size_v len3)) (as_seq h0 buff3);
  (**) SerdSpec.lemma_concat4 (size_v len1) (as_seq h0 buff1) (size_v len2) (as_seq h0 buff2)
    (size_v len3) (as_seq h0 buff3) (size_v len4) (as_seq h0 buff4) (as_seq h3 output)

let concat_buff5 #t #a #len1 #len2 #len3 #len4 #len5 buff1 buff2 buff3
  buff4 buff5 output
  = let h0 = ST.get () in
  update_sub output (size 0) len1 buff1;
  update_sub output len1 len2 buff2;
  let h1 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h1 output) 0 (size_v len1)) (as_seq h0 buff1);
  
  update_sub output (len1 +! len2) len3 buff3;
  let h2 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h2 output) 0 (size_v len1)) (as_seq h0 buff1);
  (**) Seq.eq_intro (Seq.sub (as_seq h2 output) (size_v len1) (size_v len2)) (as_seq h0 buff2);
  
  update_sub output (len1 +! len2 +! len3) len4 buff4;
  let h3 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h3 output) 0 (size_v len1)) (as_seq h0 buff1);
  (**) Seq.eq_intro (Seq.sub (as_seq h3 output) (size_v len1) (size_v len2)) (as_seq h0 buff2);
  (**) Seq.eq_intro (Seq.sub (as_seq h3 output) (size_v len1 + size_v len2) (size_v len3)) (as_seq h0 buff3);

  update_sub output (len1 +! len2 +! len3 +! len4) len5 buff5;
  let h4 = ST.get () in
  (**) Seq.eq_intro (Seq.sub (as_seq h4 output) 0 (size_v len1)) (as_seq h0 buff1);
  (**) Seq.eq_intro (Seq.sub (as_seq h4 output) (size_v len1) (size_v len2)) (as_seq h0 buff2);
  (**) Seq.eq_intro (Seq.sub (as_seq h4 output) (size_v len1 + size_v len2) (size_v len3)) (as_seq h0 buff3);
  (**) Seq.eq_intro (Seq.sub (as_seq h4 output) (size_v len1 + size_v len2 + size_v len3) (size_v len4)) (as_seq h0 buff4);
  (**) SerdSpec.lemma_concat5 (size_v len1) (as_seq h0 buff1) (size_v len2) (as_seq h0 buff2)
    (size_v len3) (as_seq h0 buff3) (size_v len4) (as_seq h0 buff4)
    (size_v len5) (as_seq h1 buff5) (as_seq h4 output)

let split_buffer #a #len s pos
  = let h0 = ST.get () in
  ST.push_frame();
  let s1 = LibBuf.sub s 0ul pos in
  let s2:(lbuffer a (size (v len - v pos))) = B.offset #a s pos in
  let h1 = ST.get () in
  (**) assert(as_seq h0 s == as_seq h1 s);
  (**) assert(length s = length s1 + length s2);
  (**) assert(as_seq h1 s1 == Seq.sub (as_seq h1 s) 0 (size_v pos));
  (**) assert(as_seq h1 s2 == Seq.sub (as_seq h1 s) (size_v pos) (size_v len - size_v pos));
  (**) assert(Seq.equal (as_seq h1 s) (Seq.concat (as_seq h1 s1) (as_seq h1 s2)));
  ST.pop_frame();
  (s1, s2)

let nat_to_bytes len buff n
  = let seq = SerdSpec.nat_to_bytes n in
  (**) assert(Seq.length seq = size_v len);
  let h0 = ST.get () in
  match (size_v len) with
    | 1 -> (
      upd buff 0ul (Seq.index seq 0);
      let h1 = ST.get () in
      (**) assert(Seq.equal (as_seq h1 buff) seq);
      ()
    )
    | 2 -> (
      upd buff 0ul (Seq.index seq 0);
      upd buff 1ul (Seq.index seq 1);
      let h1 = ST.get () in
      (**) assert(Seq.equal (as_seq h1 buff) seq);
      ()
    )
