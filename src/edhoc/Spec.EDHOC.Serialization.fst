module Spec.EDHOC.Serialization

module RIT = Lib.RawIntTypes
module Seq = Lib.Sequence
module FBytes = FStar.Bytes

module FSeq = FStar.Seq
module FSeqProp = FStar.Seq.Properties

#reset-options "--initial_fuel 2 --max_fuel 8 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 15"

/// Referenced: libsignal*
/// LSequence concatenation
let ( @< ) (#len1:size_nat) (#len2:size_nat{len1 + len2 <= max_size_t})
            (a:lbytes len1) (b:lbytes len2) : (c:lbytes (len1+len2)) =
    // As `a` and `b` are `lbytes` so we do not need explicit arguments
    // for #len in `to_seq`. Needs explicit #len argument in case
    // `a` or `b` is  `bytes`
    Seq.concat a b

let lemma_concat_alias_equiv #len1 #len2 a b
  = ()

let lemma_concat4 #a len1 s1 len2 s2 len3 s3 len4 s4 s
  = let s' = Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4 in
  FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2 + len3)) len2;
  FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2 + len3)) len2;
  FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2)) len1;
  FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2)) len1;
  FSeqProp.lemma_split s (len1 + len2);
  FSeqProp.lemma_split s' (len1 + len2);
  FSeq.lemma_eq_intro s (Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4)

let lemma_concat5 #a len1 s1 len2 s2 len3 s3 len4 s4 len5 s5 s
  = let s' = Seq.concat (Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4) s5 in
  FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2 + len3 + len4)) len3;
  FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2 + len3 + len4)) len3;
  FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2 + len3)) len2;
  FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2 + len3)) len2;
  FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2)) len1;
  FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2)) len1;
  FSeqProp.lemma_split s (len1 + len2);
  FSeqProp.lemma_split s' (len1 + len2);
  FSeq.lemma_eq_intro s (Seq.concat (Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4) s5)

let concat4 #len1 #len2 #len3 #len4 s1 s2 s3 s4
  = let s = s1 @< s2 in
  (**) FSeqProp.lemma_split s len1;
  (**) FSeqProp.lemma_split (Seq.concat s1 s2) len1;
  (**) FSeq.lemma_eq_intro s (Seq.concat s1 s2);
  (**) Seq.eq_intro s1 (Seq.sub s 0 len1);
  (**) Seq.eq_intro s2 (Seq.sub s len1 len2);
  
  // Seq.lemma_concat2 len1 s1 len2 s2 s;

  let s = s @< s3 in
  let s' = Seq.concat (Seq.concat s1 s2) s3 in
  (**) FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2)) len1;
  (**) FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2)) len1;
  (**) FSeqProp.lemma_split s (len1 + len2);
  (**) FSeqProp.lemma_split s' (len1 + len2);
  (**) FSeq.lemma_eq_intro s (Seq.concat (Seq.concat s1 s2) s3);

  let s = s @< s4 in
  let s' = Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4 in
  (**) FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2 + len3)) len2;
  (**) FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2 + len3)) len2;
  (**) FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2)) len1;
  (**) FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2)) len1;
  (**) FSeqProp.lemma_split s (len1 + len2);
  (**) FSeqProp.lemma_split s' (len1 + len2);
  (**) FSeq.lemma_eq_intro s (Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4);
  s

let lemma_concat4_comp #len1 #len2 #len3 #len4 s1 s2 s3 s4
  = ()

let concat5 #len1 #len2 #len3 #len4 #len5 s1 s2 s3 s4 s5
  = let s = concat4 s1 s2 s3 s4 in
  let s = s @< s5 in
  let s' = Seq.concat (Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4) s5 in
  (**) FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2 + len3 + len4)) len3;
  (**) FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2 + len3 + len4)) len3;
  (**) FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2 + len3)) len2;
  (**) FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2 + len3)) len2;
  (**) FSeqProp.lemma_split (Seq.sub s 0 (len1 + len2)) len1;
  (**) FSeqProp.lemma_split (Seq.sub s' 0 (len1 + len2)) len1;
  (**) FSeqProp.lemma_split s (len1 + len2);
  (**) FSeqProp.lemma_split s' (len1 + len2);
  (**) FSeq.lemma_eq_intro s (Seq.concat (Seq.concat (Seq.concat (Seq.concat s1 s2) s3) s4) s5);
  (**) assert (Seq.equal s5 (Seq.sub s (len1 + len2 + len3 + len4) len5));
  s

let lemma_concat5_comp #len1 #len2 #len3 #len4 #len5 s1 s2 s3 s4 s5
  = ()

/// Referenced: libsignal*
/// Prepend 2 bytes to the given bytes
let ( @: ) #len a b
  =
  // `nat_to_bytes_le` returns `bytes_l l` where `l` is PUB or SEC
  let prefix = nat_to_bytes_le #SEC offset a in
  ( @< ) #offset #len prefix b

/// Natural numbers Serialization/Deserialization
inline_for_extraction
let serialize_nat_to_bytes_get_length (n:size_nat)
  = (FBytes.repr_bytes n) + offset
let serialize_nat_to_bytes (n:size_nat)
  = let k = FBytes.repr_bytes n in
  k @: (nat_to_bytes n)

// /// The max_payload_size is fixed for `bytes_to_nat` as 8 bytes
let deserialize_bytes_to_nat b 
  = let len_b:nat = length b in
  let payload_size = bytes_to_nat (Seq.sub #_ #len_b b 0 offset) in
  if (payload_size > max_nof_bytes_nat
      || payload_size + offset > len_b) then Fail SerializationDeserializationFailed
  else (
    assert (offset + payload_size <= len_b);
    let payload = Seq.sub #_ #len_b b offset payload_size in
    let payload_nat = bytes_to_nat payload in
    Res (payload_nat, (payload_size + offset))
  )
  
/// Lbytes Serialization/Deserialization
inline_for_extraction
let serialize_lbytes_get_length #len lb
  : size_nat
  = len + offset
let serialize_lbytes #len lb
  = len @: lb

/// Bytes Serialization/Deserialization
inline_for_extraction
let serialize_bytes_get_length b
  : size_nat
  = (length b) + offset
let serialize_bytes b
  = (length b) @: b

let deserialize_bytes b max_payload_size start
  = let len_b = length b in
  let payload_size = bytes_to_nat (Seq.sub #_ #len_b b start offset) in
  if (payload_size > max_payload_size
      || start + offset + payload_size > len_b
      || max_payload_size > len_b
      || start + max_payload_size > len_b
      ) then Fail SerializationDeserializationFailed
  else (
    let payload = Seq.sub #_ #len_b b (start + offset) payload_size in
    assert (length payload <= max_payload_size);
    Res (payload, (start + payload_size + offset))
  )



  
