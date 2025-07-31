module Impl.EDHOC.Parser

(*HACL modules*)
open Lib.Buffer
// open Lib.Sequence
open Lib.RawIntTypes
open Lib.IntTypes
open Lib.ByteSequence
module Seq = Lib.Sequence

(*LowStar modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq

open Spec.EDHOC.CryptoPrimitives
open Impl.EDHOC.Utilities
open Impl.EDHOC.CryptoPrimitives
open TypeHelper.EDHOC

module Spec = Spec.EDHOC.Parser
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecDef = Spec.EDHOC.Base.Definitions
module SpecSerd = Spec.EDHOC.Serialization
module SpecKS = Spec.EDHOC.KeySchedule
module FBytes = FStar.Bytes

/// Many fixed-length types have been migrated to `TypeHelper` module

/// ---------------------
/// HKDF Info
/// ---------------------

/// HKDF Info | getter and setters
inline_for_extraction
type info_mem = info_label_buff & serializable_buff & okm_len_type_buff
inline_for_extraction
let construct_info_mem (label:info_label_buff) (context:serializable_buff)
  (okm:okm_len_type_buff)
  :info_mem
  = label, context, okm
inline_for_extraction
let info_mem_get_label (info:info_mem)
  :info_label_buff
  = match info with info, _, _ -> info
inline_for_extraction
let info_mem_get_context (info:info_mem)
  :serializable_buff
  = match info with _, context, _ -> context
inline_for_extraction
let info_mem_get_okm_len (info:info_mem)
  :okm_len_type_buff
  = match info with _, _, okm -> okm

let info_mem_get_length (i_mem:info_mem)
  : GTot size_t
  = match i_mem with label_buff, context_buff, okm_len_buff -> (
    size (length label_buff + length context_buff + length okm_len_buff)
  )

/// HKDF Info | predicates
let info_mem_live (h:HS.mem) (i_mem:info_mem)
  : Type0
  = match i_mem with label_buff, context_buff, okm_len_buff -> (
    live h label_buff /\ live h context_buff /\ live h okm_len_buff
  )

let info_mem_disjoint (info:info_mem)
  :Type0
  = B.all_disjoint [loc (info_mem_get_label info); loc (info_mem_get_context info);
                      loc (info_mem_get_okm_len info)]

let info_mem_disjoint_to (#t2:buftype) (#a2:Type0)
  (i_mem:info_mem) (b2:buffer_t t2 a2)
  = match i_mem with label_buff, context_buff, okm_len_buff -> (
    disjoint b2 label_buff /\ disjoint b2 context_buff /\ disjoint b2 okm_len_buff
  )
  
let info_mem_union_loc (info:info_mem)
  :GTot B.loc
  = B.loc_union (loc (info_mem_get_label info))
    (B.loc_union (loc (info_mem_get_context info))
    (loc (info_mem_get_okm_len info)))

let is_valid_info_mem_values (h:HS.mem) (i_mem:info_mem)
  = SpecSerd.bytes_to_nat (as_seq h (info_mem_get_label i_mem)) <= 12
  /\ SpecSerd.bytes_to_nat (as_seq_buff h (info_mem_get_okm_len i_mem)) <= Spec.okm_len_max_size

let is_valid_info_mem (h:HS.mem) (info:info_mem)
  :Type0
  = info_mem_live h info /\ info_mem_disjoint info
  /\ is_valid_info_mem_values h info

/// Conversion between `info` and `info_mem`
let info_mem_to_info (h:HS.mem) (i_mem:info_mem{is_valid_info_mem_values h i_mem})
  : GTot Spec.info
  = match i_mem with label_buff, context_buff, okm_buff -> (
    {
      label = SpecSerd.bytes_to_nat (as_seq h label_buff);
      context = as_seq_buff h context_buff;
      okm_len = SpecSerd.bytes_to_nat (as_seq_buff h okm_buff)
    }
  )

let lemma_info_mem_to_info (h:HS.mem) (i_mem:info_mem{is_valid_info_mem_values h i_mem})
  : Lemma (ensures (
    let info_abstract = info_mem_to_info h i_mem in
    let label_bytes = SpecSerd.nat_to_bytes info_abstract.label in
    let context_lbytes:lbytes (Seq.length info_abstract.context) = info_abstract.context in
    let okm_len_bytes = SpecSerd.nat_to_bytes info_abstract.okm_len in

    match i_mem with label_buff, context_buff, okm_len_buff -> (

      Seq.equal label_bytes (as_seq h label_buff)
      /\ Seq.equal context_lbytes (as_seq_buff h context_buff)
      /\ Seq.equal okm_len_bytes (as_seq_buff h okm_len_buff)
    )
  ))
  [SMTPat (info_mem_to_info h i_mem)]
  = ()

let lemma_info_mem_to_info_length_equiv (h:HS.mem)
  (i_mem:info_mem{is_valid_info_mem_values h i_mem})
  : Lemma (ensures (
    let info_abstract = info_mem_to_info h i_mem in

    SpecKS.concat_info_get_length info_abstract = size_v (info_mem_get_length i_mem)
  ))
  [SMTPat (info_mem_to_info h i_mem)]
  = let info_abstract = info_mem_to_info h i_mem in
  let info_abstract_len = SpecKS.concat_info_get_length info_abstract in
  let info_mem_len = size_v (info_mem_get_length i_mem) in

  assert(FBytes.repr_bytes info_abstract.okm_len
    = length (info_mem_get_okm_len i_mem));
  assert(FBytes.repr_bytes info_abstract.label
    = length (info_mem_get_label i_mem));
  assert(Seq.length info_abstract.context = length (info_mem_get_context i_mem));
  assert(info_abstract_len = (match i_mem with label_buff, context_buff, okm_buff -> (
    length label_buff + length context_buff + length okm_buff
  )));
  assert(info_mem_len = (match i_mem with _, context_buff, okm_buff -> (
    1 + length context_buff + length okm_buff
  )))

/// Concatenation of all components of `info_mem`
val concat_info_mem:
  context_len:size_t{size_v context_len <= max_size_t}
  -> okm_len_byte_len:size_t{size_v okm_len_byte_len <= 2}
  -> i_mem:info_mem
  -> i_buff:lbuffer uint8 (info_mem_get_length i_mem)
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 i_buff /\ is_valid_info_mem h0 i_mem
    /\ info_mem_disjoint_to i_mem i_buff
    /\ (
      match i_mem with _, context_buff, okm_len_buff -> (
        length context_buff = size_v context_len
        /\ length okm_len_buff = size_v okm_len_byte_len
      )
    )
  ))
  (ensures fun h0 _ h1 -> (
    let info_abstract = info_mem_to_info h0 i_mem in
    let info_abstract_concat = SpecKS.concat_info info_abstract in

    modifies1 i_buff h0 h1
    /\ Seq.equal info_abstract_concat (as_seq h1 i_buff)
  ))

/// -------------------------
/// Context 2
/// -------------------------

/// context2 struct | getter and setter
inline_for_extraction
type context2_mem (#cs:supported_cipherSuite) = c_id_buff & id_cred_buff & hash_out_buff cs & cred_buff & ead_buff
inline_for_extraction
let construct_context2_mem (#cs:supported_cipherSuite) (c_r:c_id_buff)
  (id_cred_r:id_cred_buff) (th2:hash_out_buff cs) (cred_r:cred_buff) (ead2:ead_buff)
  = c_r, id_cred_r, th2, cred_r, ead2
inline_for_extraction
let context2_mem_get_c_r (#cs:supported_cipherSuite) (context2:context2_mem #cs)
  = match context2 with c_r, _ , _, _, _ -> c_r
inline_for_extraction
let context2_mem_get_id_cred_r (#cs:supported_cipherSuite) (context2:context2_mem #cs)
  = match context2 with _, id_cred_r, _, _, _ -> id_cred_r
inline_for_extraction
let context2_mem_get_th2 (#cs:supported_cipherSuite) (context2:context2_mem #cs)
  = match context2 with _, _, th2, _, _ -> th2
inline_for_extraction
let context2_mem_get_cred_r (#cs:supported_cipherSuite) (context2:context2_mem #cs)
  = match context2 with _, _, _, cred_r, _ -> cred_r
inline_for_extraction
let context2_mem_get_ead2 (#cs:supported_cipherSuite) (context2:context2_mem #cs)
  = match context2 with _, _, _, _, ead2 -> ead2

let context2_mem_get_length (#cs:supported_cipherSuite) (context2:context2_mem #cs)
  : GTot size_t
  = match context2 with c_r_buff, id_cred_r_buff, th2_buff, cred_r_buff, ead2_buff -> (
    let size_min = size (length c_r_buff + length id_cred_r_buff + length th2_buff
          + length cred_r_buff + length ead2_buff) in
    assert(length ead2_buff = 0);
    assert(size_min = size (Spec.c_id_size + Spec.id_cred_size + (hash_size cs) + Spec.cred_size));

    size_min
  )

let lemma_context2_mem_get_length_equiv (#cs:supported_cipherSuite)
  (context2:context2_mem #cs)
  : Lemma (ensures (
    let c2_len = context2_mem_get_length context2 in
    ( c2_len
      = size (Spec.c_id_size + Spec.id_cred_size + (hash_size cs) + Spec.cred_size))
  ))
  [SMTPat (context2_mem_get_length #cs context2)]
  = ()

/// context2 struct | predicates
let context2_mem_live (#cs:supported_cipherSuite) (h:HS.mem)
  (context2:context2_mem #cs)
  :Type0
  = live h (context2_mem_get_c_r context2) /\ live h (context2_mem_get_id_cred_r context2)
  /\ live h (context2_mem_get_cred_r context2) /\ live h (context2_mem_get_th2 context2)
  /\ live h (context2_mem_get_ead2 context2)

let context2_mem_disjoint (#cs:supported_cipherSuite) (context2:context2_mem #cs)
  = B.all_disjoint [loc (context2_mem_get_c_r context2); loc (context2_mem_get_id_cred_r context2);
                    loc (context2_mem_get_th2 context2);
                    // cred_r is excluded as cred_r = id_cred_r
                    // loc (context2_mem_get_cred_r context2);
                    loc (context2_mem_get_ead2 context2)]

let context2_mem_disjoint_to (#cs:supported_cipherSuite) (#t2:buftype) (#a2:Type0)
  (context2:context2_mem #cs) (b2:buffer_t t2 a2)
  = match context2 with c_r_buff, id_cred_r_buff, th2_buff, cred_r_buff, ead2_buff -> (
    disjoint b2 c_r_buff /\ disjoint b2 id_cred_r_buff /\ disjoint b2 th2_buff
    /\ disjoint b2 cred_r_buff /\ disjoint b2 ead2_buff
  )

let context2_mem_union_loc (#cs:supported_cipherSuite) (context2:context2_mem #cs)
  :GTot B.loc
  = B.loc_union (loc (context2_mem_get_c_r context2))
    (B.loc_union (loc (context2_mem_get_id_cred_r context2))
    (B.loc_union (loc (context2_mem_get_th2 context2))
    (B.loc_union (loc (context2_mem_get_cred_r context2))
    (loc (context2_mem_get_ead2 context2)))))

let is_valid_context2_mem (#cs:supported_cipherSuite) (h:HS.mem) (context2:context2_mem #cs)
  = context2_mem_live h context2 /\ context2_mem_disjoint context2


/// Conversion between `context2` and `context2_mem`
let context2_mem_to_context2 (#cs:supported_cipherSuite) (h:HS.mem) (context2:context2_mem #cs)
  : GTot (Spec.context2 #cs)
  = match context2 with c_r_buff, id_cred_r_buff, th2_buff, cred_r_buff, ead2_buff -> (
    {
      c_r = as_seq h c_r_buff;
      id_cred_r = as_seq h id_cred_r_buff;
      th2 = as_seq h th2_buff;
      cred_r = as_seq h cred_r_buff;
      ead2 = (if g_is_null ead2_buff then None
              else Some (nn_as_seq h ead2_buff))
    }
  )

let lemma_context2_mem_to_context2_equiv (#cs:supported_cipherSuite) (h:HS.mem)
  (context2:context2_mem #cs)
  : Lemma (ensures (
    let context2_abstract = context2_mem_to_context2 h context2 in

    match context2 with c_r_buff, id_cred_r_buff, th2_buff, cred_r_buff, ead2_buff -> (

      Seq.equal context2_abstract.c_r (as_seq h c_r_buff)
      /\ Seq.equal context2_abstract.id_cred_r (as_seq h id_cred_r_buff)
      /\ Seq.equal context2_abstract.th2 (as_seq h th2_buff)
      /\ Seq.equal context2_abstract.cred_r (as_seq h cred_r_buff)
      /\ (~(g_is_null ead2_buff) <==> Some? context2_abstract.ead2)
      /\ (~(g_is_null ead2_buff) ==> (
        let ead2_v = Some?.v context2_abstract.ead2 in
        let ead2_v:lbytes (Seq.length ead2_v) = ead2_v in

        Seq.equal ead2_v (nn_as_seq h ead2_buff)
      ))
    )
  ))
  [SMTPat (context2_mem_to_context2 #cs h context2)]
  = ()

/// Concatenation of all components of `context2_mem`
val concat_context2_mem:
  #cs:supported_cipherSuite
  -> context2:context2_mem #cs
  -> context2_buff:lbuffer uint8 (context2_mem_get_length context2)
  -> ST.Stack unit
  (requires fun h0 -> (
    is_valid_context2_mem h0 context2 /\ live h0 context2_buff
    /\ context2_mem_disjoint_to context2 context2_buff
  ))
  (ensures fun h0 _ h1 -> (
    let context2_abstract = context2_mem_to_context2 h0 context2 in
    let context2_abstract_concat = SpecKS.concat_context2 context2_abstract in

    modifies1 context2_buff h0 h1
    /\ Seq.equal context2_abstract_concat (as_seq h1 context2_buff)
  ))

/// -------------------------
/// Context 3
/// -------------------------

/// context3 struct | getters and setter
inline_for_extraction
type context3_mem (#cs:supported_cipherSuite)
  = id_cred_buff & hash_out_buff cs & cred_buff & ead_buff
inline_for_extraction
let construct_context3_mem (#cs:supported_cipherSuite) (id_cred_i:id_cred_buff)
  (th3:hash_out_buff cs) (cred_i:cred_buff) (ead3:ead_buff)
  = id_cred_i, th3, cred_i, ead3
inline_for_extraction
let context3_mem_get_id_cred_i (#cs:supported_cipherSuite) (context3:context3_mem #cs)
  = match context3 with id_cred_i, _, _, _ -> id_cred_i
inline_for_extraction
let context3_mem_get_th3 (#cs:supported_cipherSuite) (context3:context3_mem #cs)
  = match context3 with _, th3, _, _ -> th3
inline_for_extraction
let context3_mem_get_cred_i (#cs:supported_cipherSuite) (context3:context3_mem #cs)
  = match context3 with _, _, cred_i, _ -> cred_i
inline_for_extraction
let context3_mem_get_ead3 (#cs:supported_cipherSuite) (context3:context3_mem #cs)
  = match context3 with _, _, _, ead3 -> ead3

let context3_mem_get_length (#cs:supported_cipherSuite) (context3:context3_mem #cs)
  : GTot size_t
  = match context3 with id_cred_i_buff, th3_buff, cred_i_buff, ead3_buff -> (
    let size_min = size (length id_cred_i_buff + length th3_buff + length cred_i_buff
                    + length ead3_buff) in
    assert(g_is_null ead3_buff ==> length ead3_buff = 0);
    assert(size_min = size (Spec.id_cred_size + (hash_size cs) + Spec.cred_size));
    size_min
  )

let lemma_context3_mem_get_length_equiv (#cs:supported_cipherSuite) (context3:context3_mem #cs)
  : Lemma (ensures (
    context3_mem_get_length context3
      = size (
        Spec.id_cred_size + (hash_size cs) + Spec.cred_size
      )
  ))
  [SMTPat (context3_mem_get_length #cs context3)]
  = ()

/// context3 struct | predicates
let context3_mem_live (#cs:supported_cipherSuite) (h:HS.mem)
  (context3:context3_mem #cs)
  :Type0
  = live h (context3_mem_get_cred_i context3) /\ live h (context3_mem_get_id_cred_i context3)
  /\ live h (context3_mem_get_th3 context3) /\ live h (context3_mem_get_ead3 context3)

let context3_mem_disjoint (#cs:supported_cipherSuite) (context3:context3_mem #cs)
  = B.all_disjoint [
                    // cred_i is excluded as cred_i = id_cred_i
                    //loc (context3_mem_get_cred_i context3);
                    loc (context3_mem_get_id_cred_i context3);
                    loc (context3_mem_get_th3 context3); loc (context3_mem_get_ead3 context3)]

let context3_mem_disjoint_to (#cs:supported_cipherSuite)
  (#t2:buftype) (#a2:Type0)
  (context3:context3_mem #cs) (b2:buffer_t t2 a2)
  = match context3 with id_cred_i_buff, th3_buff, cred_i_buff, ead3_buff -> (
    disjoint b2 id_cred_i_buff /\ disjoint b2 th3_buff /\ disjoint b2 cred_i_buff
    /\ disjoint b2 ead3_buff
  )

let context3_mem_union_loc (#cs:supported_cipherSuite) (context3:context3_mem #cs)
  = B.loc_union (loc (context3_mem_get_id_cred_i context3))
  (B.loc_union (loc (context3_mem_get_cred_i context3))
  (B.loc_union (loc (context3_mem_get_th3 context3))
  (loc (context3_mem_get_ead3 context3))))

let is_valid_context3_mem (#cs:supported_cipherSuite) (h:HS.mem) (context3:context3_mem #cs)
  = context3_mem_live h context3 /\ context3_mem_disjoint context3

/// Conversion between `context3` and `context3_mem`
let context3_mem_to_context3 (#cs:supported_cipherSuite) (h:HS.mem)
  (context3:context3_mem #cs)
  : GTot (Spec.context3 #cs)
  = match context3 with id_cred_i_buff, th3_buff, cred_i_buff, ead3_buff -> (
    {
      id_cred_i = as_seq h id_cred_i_buff;
      th3 = as_seq h th3_buff;
      cred_i = as_seq h cred_i_buff;
      ead3 = (if g_is_null ead3_buff then None
              else Some (nn_as_seq h ead3_buff))
    }
  )

let lemma_context3_mem_to_context3_equiv (#cs:supported_cipherSuite) (h:HS.mem)
  (context3:context3_mem #cs)
  : Lemma (ensures (
    let context3_abstract = context3_mem_to_context3 h context3 in

    match context3 with id_cred_i_buff, th3_buff, cred_i_buff, ead3_buff -> (

      Seq.equal context3_abstract.id_cred_i (as_seq h id_cred_i_buff)
      /\ Seq.equal context3_abstract.th3 (as_seq h th3_buff)
      /\ Seq.equal context3_abstract.cred_i (as_seq h cred_i_buff)
      /\ (~(g_is_null ead3_buff) <==> Some? context3_abstract.ead3)
      /\ (~(g_is_null ead3_buff) ==> (
        let ead3_v = Some?.v context3_abstract.ead3 in
        let ead3_v:lbytes (Seq.length ead3_v) = ead3_v in

        Seq.equal ead3_v (nn_as_seq h ead3_buff)
      ))
    )
  ))
  [SMTPat (context3_mem_to_context3 #cs h context3)]
  = ()

/// Concatenation of all components of `context3_mem`
val concat_context3_mem:
  #cs:supported_cipherSuite
  -> context3:context3_mem #cs
  -> context3_buff:lbuffer uint8 (context3_mem_get_length context3)
  -> ST.Stack unit
  (requires fun h0 -> (
    is_valid_context3_mem h0 context3 /\ live h0 context3_buff
    /\ context3_mem_disjoint_to context3 context3_buff
  ))
  (ensures fun h0 _ h1 -> (
    let context3_abstract = context3_mem_to_context3 h0 context3 in
    let context3_abstract_concat = SpecKS.concat_context3 context3_abstract in

    modifies1 context3_buff h0 h1
    /\ Seq.equal context3_abstract_concat (as_seq h1 context3_buff)
  ))


/// -------------------------
/// Message 1
/// -------------------------

/// `message1_mem` setter and getters
inline_for_extraction
type message1_mem (#cs:supported_cipherSuite)
  = method_buff & suite_buff & ec_pub_key_buf cs & c_id_buff & ead_buff

inline_for_extraction
let message1_mem_get_length (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  :GTot (res:size_t{size_v res <= max_size_t})
  = match msg1 with method, suite, pubkey, c_id, ead1 -> (
    let size_min = size (length method + length suite + length pubkey + length c_id + length ead1) in
    assert(g_is_null ead1 ==> length ead1 = 0);
    size_min
  )

let lemma_message1_mem_get_length_ead1_consistence
  (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  : Lemma (ensures (
    message1_mem_get_length #cs msg1
      = size (
        match msg1 with method, suite, pubkey, c_id, ead1 ->
          (
            let temp = length method + length suite + length pubkey + length c_id in
            if g_is_null ead1 then temp
            else (temp + length ead1)
          )
      )
  ))
  [SMTPat (message1_mem_get_length #cs msg1)]
  = ()

inline_for_extraction
let construct_message1_mem (#cs:supported_cipherSuite) (method:method_buff)
  (suite_i:suite_buff) (g_x:ec_pub_key_buf cs) (c_i:c_id_buff) (ead1:ead_buff)
  = method, suite_i, g_x, c_i, ead1
inline_for_extraction
let message1_mem_get_method (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  :method_buff
  = match msg1 with method, _, _, _ , _ -> method
inline_for_extraction
let message1_mem_get_suite_i (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  :suite_buff
  = match msg1 with _, suite_i, _, _, _ -> suite_i
inline_for_extraction
let message1_mem_get_g_x (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  :ec_pub_key_buf cs
  = match msg1 with _, _, g_x, _, _ -> g_x
inline_for_extraction
let message1_mem_get_c_i (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  :c_id_buff
  = match msg1 with _, _, _, c_i, _ -> c_i
inline_for_extraction
let message1_mem_get_ead1 (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  :ead_buff
  = match msg1 with _, _, _, _, ead1 -> ead1

/// `message1_mem` predicates
let message1_mem_live (#cs:supported_cipherSuite) (h:HS.mem) (msg1:message1_mem #cs)
  = live h (message1_mem_get_c_i msg1) /\ live h (message1_mem_get_method msg1)
    /\ live h (message1_mem_get_suite_i msg1) /\ live h (message1_mem_get_g_x msg1)
    /\ live h (message1_mem_get_ead1 msg1)

let message1_mem_disjoint (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  = let ead1 = message1_mem_get_ead1 msg1 in
    B.all_disjoint [loc (message1_mem_get_method msg1); loc (message1_mem_get_suite_i msg1);
                    loc (message1_mem_get_g_x msg1); loc (message1_mem_get_c_i msg1);
                    loc (message1_mem_get_ead1 msg1)]

let message1_mem_union_loc (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  = match msg1 with method_m, suite_i_m, g_x_m, c_i_m, ead1_m -> (
    B.loc_union (loc method_m)
    (B.loc_union (loc suite_i_m)
    (B.loc_union (loc g_x_m)
    (B.loc_union (loc c_i_m)
    (loc ead1_m))))
  )

let message1_mem_union_loc_non_ead1 (#cs:supported_cipherSuite) (msg1:message1_mem #cs)
  = match msg1 with method_m, suite_i_m, g_x_m, c_i_m, ead1_m -> (
    loc method_m |+| loc suite_i_m |+| loc g_x_m |+| loc c_i_m
  )


let modifies_msg1_mem (#cs:supported_cipherSuite)
  (msg1_m:message1_mem #cs) (h0 h1:HS.mem)
  = modifies (message1_mem_union_loc msg1_m) h0 h1

let message1_mem_disjoint_to (#t2:buftype) (#a2:Type0) (#cs:supported_cipherSuite)
  (msg1:message1_mem #cs) (b2:buffer_t t2 a2) 
  = B.loc_disjoint (message1_mem_union_loc msg1) (loc b2)

let lemma_message1_mem_disjoint_to (#t2:buftype) (#a2:Type0) (#cs:supported_cipherSuite)
  (msg1:message1_mem #cs) (b2:buffer_t t2 a2)
  : Lemma (ensures (
    message1_mem_disjoint_to msg1 b2 ==> (
      match msg1 with method_m, suite_i_m, g_x_m, c_i_m, ead1_m -> (
        disjoint method_m b2 /\ disjoint suite_i_m b2
        /\ disjoint g_x_m b2 /\ disjoint c_i_m b2 /\ disjoint ead1_m b2
      )
    )
  ))
  [SMTPat (message1_mem_disjoint_to #t2 #a2 #cs msg1 b2)]
  = ()

let is_valid_message1_mem (#cs:supported_cipherSuite) (h:HS.mem) (msg1:message1_mem #cs)
  = message1_mem_live h msg1 /\ message1_mem_disjoint msg1

let is_valid_message1_mem_after_init (#cs:supported_cipherSuite) (h:HS.mem) (msg1:message1_mem #cs)
  = is_valid_message1_mem h msg1 /\ (
    // let method_label = SpecSerd.bytes_to_nat (as_seq h (message1_mem_get_method msg1)) in
    // let suite_i_label = SpecSerd.bytes_to_nat (as_seq h (message1_mem_get_suite_i msg1)) in
    let method_label = uint_to_nat (bget h (message1_mem_get_method msg1) 0) in
    let suite_i_label = uint_to_nat (bget h (message1_mem_get_suite_i msg1) 0) in
    method_label > 0 /\ method_label <= 4 /\ suite_i_label >= 6 /\ suite_i_label <= 7
  )

/// Conversion between `message1` and `message1_mem`
let eval_message1_mem (#cs:supported_cipherSuite)
  (h:HS.mem) (msg1_mem:message1_mem #cs{is_valid_message1_mem_after_init h msg1_mem})
  : GTot (Spec.message1 #cs)
  = 
  let method_label = uint_to_nat (bget h (message1_mem_get_method msg1_mem) 0) in
  assert(method_label <= 4);
  let method = SpecDef.label_to_method method_label in
  assert(method_label = SpecDef.method_as_nat method);
  let suite_i = uint_to_nat (bget h (message1_mem_get_suite_i msg1_mem) 0) in

  let msg1: Spec.message1 #cs = {
    method = method;
    suite_i = suite_i;
    g_x = as_seq h (message1_mem_get_g_x msg1_mem);
    c_i = as_seq h (message1_mem_get_c_i msg1_mem);
    ead1 = (
      let ead1_buff = (message1_mem_get_ead1 msg1_mem) in
      if (g_is_null ead1_buff || length ead1_buff = 0) then None
      else Some (nn_as_seq h ead1_buff)
    )
  } in
  msg1


/// This lemma ensures the equivalence between abstract and
/// low-level model of `msg1` struct
let lemma_eval_message1_mem (#cs:supported_cipherSuite)
  (h:HS.mem) (msg1_mem:message1_mem #cs)
  : Lemma (requires is_valid_message1_mem_after_init h msg1_mem)
  (ensures (
    let msg1 = eval_message1_mem #cs h msg1_mem in
    let ead1_buff = (message1_mem_get_ead1 msg1_mem) in
    (~((g_is_null ead1_buff) \/ length ead1_buff = 0) <==> Some? msg1.ead1)
    /\ Seq.equal (as_seq h (message1_mem_get_method msg1_mem)) (
      let method_lbyte:lbytes 1 = SpecSerd.nat_to_bytes (SpecDef.method_as_nat msg1.method) in
      method_lbyte
    )
    /\ uint_to_nat (bget h (message1_mem_get_suite_i msg1_mem) 0) = msg1.suite_i
    /\ Seq.equal (as_seq h (message1_mem_get_g_x msg1_mem)) msg1.g_x
    /\ Seq.equal (as_seq h (message1_mem_get_c_i msg1_mem)) msg1.c_i
    /\ ((~(g_is_null ead1_buff) /\ length ead1_buff > 0) ==> (
      let ead1_v = Some?.v msg1.ead1 in
      let ead1_v_lbytes:lbytes (Seq.length ead1_v) = ead1_v in
      Seq.equal (nn_as_seq h ead1_buff ) ead1_v_lbytes
    ))
  ))
  [SMTPat (eval_message1_mem #cs h msg1_mem)]
  = ()


val concat_msg1_mem:
  #cs:supported_cipherSuite
  -> msg1:message1_mem #cs
  -> msg1_buff:lbuffer uint8 (message1_mem_get_length msg1)
  -> ST.Stack unit
  (requires fun h0 -> is_valid_message1_mem_after_init h0 msg1
    /\ message1_mem_disjoint_to msg1 msg1_buff
    /\ live h0 msg1_buff
  )
  (ensures fun h0 _ h1 -> modifies1 msg1_buff h0 h1
    /\ (
      let msg1_abstract = eval_message1_mem #cs h0 msg1 in
      let msg1_abstract_concat = (Spec.concat_msg1 #cs msg1_abstract) in
      let msg1_len = Seq.length msg1_abstract_concat in
      let msg1_abstract_concat:lbytes msg1_len = msg1_abstract_concat in

      Seq.equal (as_seq h1 msg1_buff) (msg1_abstract_concat)
    )
  )


/// -------------------------
/// Plaintext 2
/// -------------------------
inline_for_extraction
let plaintext2_len_fixed_v (cs:supported_cipherSuite) (auth_material:authentication_material)
  = size (Spec.c_id_size + Spec.id_cred_size +
            Spec.sig_or_mac23_size cs auth_material + Spec.ead_max_size)

inline_for_extraction
type plaintext2_mem (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  = c_id_buff & id_cred_buff & sig_or_mac23_buff cs auth_material
  & ead_buff

inline_for_extraction
let plaintext2_mem_get_length (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx2:plaintext2_mem #cs #auth_material)
  = match ptx2 with c_r, id_cred_r, sig_or_mac2, ead2 -> (
    let size_min = size (length c_r + length id_cred_r + length sig_or_mac2 + length ead2) in
    assert(g_is_null ead2 ==> length ead2 = 0);
    assert(size_min = size (Spec.c_id_size + Spec.id_cred_size +
                   Spec.sig_or_mac23_size cs auth_material));
    assert(size_min = size (Spec.c_id_size + Spec.id_cred_size +
                   Spec.sig_or_mac23_size cs auth_material + Spec.ead_max_size));
    size_min
  )

let lemma_plaintext2_mem_get_length_ead2_consistence
  (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx2:plaintext2_mem #cs #auth_material)
  : Lemma (ensures (
    let ptx2_len = plaintext2_mem_get_length #cs #auth_material ptx2 in
    (ptx2_len = size (Spec.c_id_size + Spec.id_cred_size +
                   Spec.sig_or_mac23_size cs auth_material))
    /\ ptx2_len = plaintext2_len_fixed_v cs auth_material
    /\ size_v ptx2_len <= max_size_t
  ))
  [SMTPat (plaintext2_mem_get_length #cs #auth_material ptx2)]
  = ()

/// `plaintext2_mem` constructor | getters
inline_for_extraction
let construct_plaintext2_mem (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (c_r:c_id_buff) (id_cred_r:id_cred_buff) (sig_or_mac2:sig_or_mac23_buff cs auth_material)
  (ead2:ead_buff)
  = c_r, id_cred_r, sig_or_mac2, ead2
inline_for_extraction
let plaintext2_mem_get_c_r (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx2:plaintext2_mem #cs #auth_material)
  = match ptx2 with c_r, _, _, _ -> c_r
inline_for_extraction
let plaintext2_mem_get_id_cred_r (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx2:plaintext2_mem #cs #auth_material)
  = match ptx2 with _, id_cred_r, _, _ -> id_cred_r
inline_for_extraction
let plaintext2_mem_get_sig_or_mac2 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx2:plaintext2_mem #cs #auth_material)
  = match ptx2 with _, _, sig_or_mac2, _ -> sig_or_mac2
inline_for_extraction
let plaintext2_mem_get_ead2 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx2:plaintext2_mem #cs #auth_material)
  = match ptx2 with _, _, _, ead2 -> ead2

/// `plaintext2_mem` predicates
let plaintext2_mem_live (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (ptx2:plaintext2_mem #cs #auth_material)
  = live h (plaintext2_mem_get_c_r ptx2) /\ live h (plaintext2_mem_get_id_cred_r ptx2)
  /\ live h (plaintext2_mem_get_sig_or_mac2 ptx2)
  /\ live h (plaintext2_mem_get_ead2 ptx2)

let plaintext2_mem_disjoint (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx2:plaintext2_mem #cs #auth_material)
  = B.all_disjoint [loc (plaintext2_mem_get_c_r ptx2); loc (plaintext2_mem_get_id_cred_r ptx2);
                    loc (plaintext2_mem_get_sig_or_mac2 ptx2); loc (plaintext2_mem_get_ead2 ptx2)
  ]

let plaintext2_mem_union_loc (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx2:plaintext2_mem #cs #auth_material)
  = B.loc_union (loc (plaintext2_mem_get_c_r ptx2))
  (B.loc_union (loc (plaintext2_mem_get_id_cred_r ptx2))
  (B.loc_union (loc (plaintext2_mem_get_sig_or_mac2 ptx2))
  (loc (plaintext2_mem_get_ead2 ptx2))))

let plaintext2_mem_disjoint_to_buffer (#t2:buftype) (#a2:Type0) (#cs:supported_cipherSuite)
  (#auth_material:authentication_material)
  (ptx2:plaintext2_mem #cs #auth_material) (b2:buffer_t t2 a2)
  = disjoint b2 (plaintext2_mem_get_c_r ptx2) /\ disjoint b2 (plaintext2_mem_get_id_cred_r ptx2)
  /\ disjoint b2 (plaintext2_mem_get_sig_or_mac2 ptx2) /\ disjoint b2 (plaintext2_mem_get_ead2 ptx2)

let is_valid_plaintext2_mem (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (ptx2:plaintext2_mem #cs #auth_material)
  = plaintext2_mem_live h ptx2 /\ plaintext2_mem_disjoint ptx2

/// Conversion between `plaintext2_mem` and `plaintext2`
let plaintext2_mem_to_plaintext2 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (ptx2_mem:plaintext2_mem #cs #auth_material{is_valid_plaintext2_mem h ptx2_mem})
  : GTot (Spec.plaintext2 #cs #auth_material)
  =
  let sig_or_mac2:Spec.sig_or_mac23_bytes cs auth_material
    = (as_seq h (plaintext2_mem_get_sig_or_mac2 ptx2_mem)) in

  let ptx2: Spec.plaintext2 #cs #auth_material = {
    c_r = as_seq h (plaintext2_mem_get_c_r ptx2_mem);
    id_cred_r = as_seq h (plaintext2_mem_get_id_cred_r ptx2_mem);
    sig_or_mac2 = sig_or_mac2;
    ead2 = (
      let ead2_buff = plaintext2_mem_get_ead2 ptx2_mem in
      let ead2_seq = as_seq #MUT #uint8 #(size (length ead2_buff)) h ead2_buff in
      if (g_is_null ead2_buff || length ead2_buff = 0) then None
      else Some ead2_seq
    )
  } in
  ptx2


/// This lemma ensures the equivalence between the abstract
/// and low-level computationally model of `plaintext2` struct
let lemma_plaintext2_mem_to_plaintext2_equiv
  (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (ptx2_mem:plaintext2_mem #cs #auth_material)
  : Lemma (requires is_valid_plaintext2_mem #cs #auth_material h ptx2_mem)
  (ensures (
    let ptx2 = plaintext2_mem_to_plaintext2 #cs #auth_material h ptx2_mem in
    let ead2_buff = plaintext2_mem_get_ead2 ptx2_mem in

    (~((g_is_null ead2_buff) \/ length ead2_buff = 0) <==> Some? ptx2.ead2)
    /\ Seq.equal ptx2.c_r (as_seq h (plaintext2_mem_get_c_r ptx2_mem))
    /\ Seq.equal ptx2.id_cred_r (as_seq h (plaintext2_mem_get_id_cred_r ptx2_mem))
    /\ Seq.equal ptx2.sig_or_mac2 (as_seq h (plaintext2_mem_get_sig_or_mac2 ptx2_mem))
    /\ ((~(g_is_null ead2_buff) /\ length ead2_buff > 0) ==> (
      let ead2_v = Some?.v ptx2.ead2 in
      let ead2_v_lbytes:lbytes (Seq.length ead2_v) = ead2_v in
      Seq.equal (nn_as_seq h ead2_buff ) ead2_v_lbytes
    ))
  ))
  [SMTPat (plaintext2_mem_to_plaintext2 #cs #auth_material h ptx2_mem)]
  = ()

inline_for_extraction noextract
type concat_ptx2_st =
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> #ptx2_len:size_t
  -> ptx2:plaintext2_mem #cs #auth_material
  -> ptx2_buff:lbuffer uint8 ptx2_len
  -> ST.Stack unit
  (requires fun h0 -> ( ptx2_len = (plaintext2_mem_get_length ptx2) /\
    live h0 ptx2_buff /\
    is_valid_plaintext2_mem h0 ptx2
    /\ plaintext2_mem_disjoint_to_buffer ptx2 ptx2_buff
  ))
  (ensures fun h0 _ h1 -> ( modifies1 ptx2_buff h0 h1
    /\ (
      let ptx2_abstract = plaintext2_mem_to_plaintext2 #cs #auth_material h0 ptx2 in
      let ptx2_abstract_concat = Spec.concat_ptx2 #cs #auth_material ptx2_abstract in
      let ptx2_abstract_concat:lbytes (Seq.length ptx2_abstract_concat) = ptx2_abstract_concat in

      Seq.equal ptx2_abstract_concat (as_seq h1 ptx2_buff)
    )
  ))

val concat_ptx2_mem: concat_ptx2_st

inline_for_extraction
let serialize_ptx2_mem: concat_ptx2_st
  = concat_ptx2_mem

val deserialize_ptx2_mem:
  // #len_ead2:size_t
  cs:supported_cipherSuite
  -> auth_material:authentication_material
  // -> len_ptx2:size_t{len_ptx2 = plaintext2_len_fixed_v cs auth_material}
  // -> #len_c_r:size_t{size_v len_c_r = Spec.c_id_size}
  // -> #len_id_cred_r:size_t{size_v len_id_cred_r = Spec.id_cred_size}
  // -> #len_sig_or_mac2:size_t{size_v len_sig_or_mac2 = Spec.sig_or_mac23_size cs auth_material}
  -> serialized_ptx2_mem:lbuffer uint8 (plaintext2_len_fixed_v cs auth_material)
  -> c_r_buff:c_id_buff
  -> id_cred_r_buff:id_cred_buff
  -> sig_or_mac2_buff:lbuffer uint8 (sig_or_mac23_size_v cs auth_material)
  -> ead2_buff:ead_buff
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 serialized_ptx2_mem /\ live h0 c_r_buff /\ live h0 id_cred_r_buff
    /\ live h0 sig_or_mac2_buff /\ live h0 ead2_buff
    /\ B.all_disjoint [loc serialized_ptx2_mem; loc c_r_buff; loc id_cred_r_buff;
                      loc sig_or_mac2_buff; loc ead2_buff]
    // /\ (
    //     let len_c_r = size (Spec.id_cred_size) in
    //     let len_id_cred_r = size Spec.id_cred_size in
    //     let len_sig_or_mac2 = size (Spec.sig_or_mac23_size cs auth_material) in
    //     let len_ptx2 = (plaintext2_len_fixed_v cs auth_material) in
    //   size_v len_ead2 < Spec.ead_max_size
    //   /\ size_v (len_c_r +! len_id_cred_r +! len_sig_or_mac2 +! len_ead2) = size_v len_ptx2
    // )
  ))
  (ensures fun h0 _ h1 -> ( 
    (g_is_null ead2_buff ==> modifies3 c_r_buff id_cred_r_buff sig_or_mac2_buff h0 h1)
    /\ (
      let (c_r, id_cred_r, sig_or_mac2, ead2)
        = Spec.deserialize_ptx2_raw_bytes cs auth_material (as_seq h0 serialized_ptx2_mem) in

      Seq.equal c_r (as_seq h1 c_r_buff)
      /\ Seq.equal id_cred_r (as_seq h1 id_cred_r_buff)
      /\ Seq.equal sig_or_mac2 (as_seq h1 sig_or_mac2_buff)
      // no need to check EAD2 currently as EAD is not supported
      /\ (Some? ead2 /\ (Seq.length (Some?.v ead2) > 0 /\ ~(g_is_null ead2_buff)) ==> (
        let ead2 = Some?.v ead2 in
        let ead2:lbytes (Seq.length ead2) = ead2 in

        modifies4 c_r_buff id_cred_r_buff sig_or_mac2_buff ead2_buff h0 h1 /\
        Seq.equal ead2 (nn_as_seq h1 ead2_buff)
      ))
    )
  ))

/// -------------------------
/// Message 2
/// -------------------------

/// Definition
inline_for_extraction
type message2_mem (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  = (ec_pub_key_buf cs) & (ciphertext2_buff cs auth_material)

/// Constructor
inline_for_extraction
let construct_message2_mem (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (g_y:ec_pub_key_buf cs) (ciphertext2:ciphertext2_buff cs auth_material)
  = g_y, ciphertext2

/// Getters
inline_for_extraction
let message2_mem_get_g_y (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (msg2:message2_mem #cs #auth_material)
  = match msg2 with g_y, _ -> g_y
inline_for_extraction
let message2_mem_get_ciphertext2 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (msg2:message2_mem #cs #auth_material)
  = match msg2 with _, c2 -> c2

inline_for_extraction
let message2_mem_get_length (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (msg2:message2_mem #cs #auth_material)
  : GTot (res:size_t{size_v res <= max_size_t})
  = match msg2 with g_y, c2 -> (
    size (length g_y + length c2)
  )

let lemma_message2_mem_get_length_equiv (#cs:supported_cipherSuite)
  (#auth_material:authentication_material)
  (msg2:message2_mem #cs #auth_material)
  : Lemma (ensures (
    let msg2_len = message2_mem_get_length msg2 in

    msg2_len = (match msg2 with g_y, c2 -> (
        size (length c2 + SpecCrypto.ec_pub_key_size (SpecCrypto.get_ec_alg cs))
      ))
  ))
  [SMTPat (message2_mem_get_length #cs #auth_material msg2)]
  = ()

/// `message2_mem` Predicates
let message2_mem_live (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (msg2:message2_mem #cs #auth_material)
  = match msg2 with g_y, c2 -> live h g_y /\ live h c2

let message2_mem_disjoint (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (msg2:message2_mem #cs #auth_material)
  = match msg2 with g_y, c2 -> B.all_disjoint [loc (g_y); loc (c2)]

let message2_mem_union_loc (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (msg2:message2_mem #cs #auth_material)
  = match msg2 with g_y, c2 -> B.loc_union (loc g_y) (loc c2)

let message2_mem_disjoint_to (#t2:buftype) (#a2:Type0) (#cs:supported_cipherSuite)
  (#auth_material:authentication_material) (msg2:message2_mem #cs #auth_material)
  (b2:buffer_t t2 a2)
  = match msg2 with g_y, c2 -> disjoint b2 g_y /\ disjoint b2 c2

let is_valid_message2_mem (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (msg2:message2_mem #cs #auth_material)
  = message2_mem_live h msg2 /\ message2_mem_disjoint msg2

/// Conversion between `message2` and `message2_mem`
let message2_mem_to_msg2 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (msg2_mem:message2_mem #cs #auth_material{is_valid_message2_mem h msg2_mem})
  : GTot (Spec.message2 #cs #auth_material)
  = match msg2_mem with g_y, c2 -> (
    // let c2:lbuffer uint8 (size (length c2)) = c2 in
    let msg2:Spec.message2 #cs #auth_material = {
      g_y = (as_seq h g_y);
      ciphertext2 = (as_seq h c2)
    }
    in
    msg2
  )
 

/// This lemma ensures the equivalence between abstract and
/// low-level model of `msg2` struct
let lemma_message2_mem_to_msg2 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (msg2_mem:message2_mem #cs #auth_material)
  : Lemma (requires (
    is_valid_message2_mem h msg2_mem
  ))
  (ensures (
    let msg2 = message2_mem_to_msg2 #cs #auth_material h msg2_mem in
    let ciphertext2 = (message2_mem_get_ciphertext2 msg2_mem) in
    let ciphertext2:lbuffer uint8 (size (length ciphertext2)) = ciphertext2 in
    
    Seq.equal msg2.g_y (as_seq h (message2_mem_get_g_y msg2_mem))
    /\ Seq.equal msg2.ciphertext2 (as_seq h ciphertext2)
  ))
  [SMTPat (message2_mem_to_msg2 #cs #auth_material h msg2_mem)]
  = ()

inline_for_extraction noextract
type concat_msg2_mem_st =
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> msg2_mem:message2_mem #cs #auth_material
  -> msg2_buff:lbuffer uint8 (message2_mem_get_length msg2_mem)
  -> ST.Stack unit
  (requires fun h0 -> (
    is_valid_message2_mem h0 msg2_mem
    /\ live h0 msg2_buff
    /\ message2_mem_disjoint_to msg2_mem msg2_buff
  ))
  (ensures fun h0 _ h1 -> (
    let msg2_abstract = message2_mem_to_msg2 h0 msg2_mem in
    let msg2_abstract_concat = Spec.serialize_msg2 msg2_abstract in
    let msg2_abstract_concat:lbytes (Seq.length msg2_abstract_concat) = msg2_abstract_concat in

    modifies1 msg2_buff h0 h1
    /\ Seq.equal msg2_abstract_concat (as_seq h1 msg2_buff)
  ))

val concat_msg2_mem: concat_msg2_mem_st

inline_for_extraction
let serialize_msg2_mem: concat_msg2_mem_st
  = concat_msg2_mem


/// -------------------------
/// Plaintext 3
/// -------------------------

/// Definition
inline_for_extraction
type plaintext3_mem (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  = id_cred_buff & sig_or_mac23_buff cs auth_material & ead_buff

inline_for_extraction
let plaintext3_len_fixed_v (cs:supported_cipherSuite) (auth_material:authentication_material)
  = size (Spec.id_cred_size + Spec.sig_or_mac23_size cs auth_material + Spec.ead_max_size)

/// Constructor
inline_for_extraction
let construct_plaintext3_mem (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (id_cred_i:id_cred_buff) (sig_or_mac3:sig_or_mac23_buff cs auth_material)
  (ead3:ead_buff)
  = id_cred_i, sig_or_mac3, ead3

inline_for_extraction
let plaintext3_mem_get_length (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx3:plaintext3_mem #cs #auth_material)
  : GTot (res:size_t{Spec.is_valid_ptx3_size cs auth_material (size_v res)})
  = match ptx3 with id_cred_i, sig_or_mac3, ead3 -> (
    let size_min = size (length id_cred_i + length sig_or_mac3 + length ead3) in
    assert(g_is_null ead3 ==> length ead3 = 0);
    size_min
  )

let lemma_plaintext3_mem_get_length_consistence
  (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx3:plaintext3_mem #cs #auth_material)
  : Lemma (ensures (
    plaintext3_mem_get_length ptx3
      = plaintext3_len_fixed_v cs auth_material
  ))
  [SMTPat (plaintext3_mem_get_length #cs #auth_material ptx3)]
  = ()

/// Getters
inline_for_extraction
let plaintext3_mem_get_id_cred_i (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx3_mem:plaintext3_mem #cs #auth_material)
  = match ptx3_mem with id_cred_i, _, _ -> id_cred_i
inline_for_extraction
let plaintext3_mem_get_sig_or_mac3 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx3_mem:plaintext3_mem #cs #auth_material)
  = match ptx3_mem with _, sig_or_mac3, _ -> sig_or_mac3
inline_for_extraction
let plaintext3_mem_get_ead3 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx3_mem:plaintext3_mem #cs #auth_material)
  = match ptx3_mem with _, _, ead3 -> ead3

/// `plaintext3_mem` predicates
let plaintext3_mem_live (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (ptx3:plaintext3_mem #cs #auth_material)
  = match ptx3 with id_cred_i, sig_or_mac3, ead3 ->
    live h id_cred_i /\ live h sig_or_mac3 /\ live h ead3

let plaintext3_mem_disjoint (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx3:plaintext3_mem #cs #auth_material)
  = match ptx3 with id_cred_i, sig_or_mac3, ead3 ->
    B.all_disjoint [loc id_cred_i; loc sig_or_mac3; loc ead3]

let plaintext3_mem_union_loc (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx3:plaintext3_mem #cs #auth_material)
  = match ptx3 with id_cred_i, sig_or_mac3, ead3 ->
    B.loc_union (loc id_cred_i)
    (B.loc_union (loc sig_or_mac3) (loc ead3))

let plaintext3_mem_disjoint_to_buffer (#t2:buftype) (#a2:Type0)
  (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (ptx3:plaintext3_mem #cs #auth_material) (b2:buffer_t t2 a2)
  = match ptx3 with id_cred_i, sig_or_mac3, ead3 ->
    disjoint b2 id_cred_i /\ disjoint b2 sig_or_mac3 /\ disjoint b2 ead3

let is_valid_plaintext3_mem (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (ptx3:plaintext3_mem #cs #auth_material)
  = plaintext3_mem_live h ptx3 /\ plaintext3_mem_disjoint ptx3

/// Conversion between `plaintext3_mem` and `plaintext3`
let plaintext3_mem_to_plaintext3 (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (ptx3_mem:plaintext3_mem #cs #auth_material{is_valid_plaintext3_mem h ptx3_mem})
  : GTot (Spec.plaintext3 #cs #auth_material)
  = match ptx3_mem with id_cred_i, sig_or_mac3, ead3 -> (
    {
      id_cred_i = (as_seq h id_cred_i);
      sig_or_mac3 = (as_seq h sig_or_mac3);
      ead3 = (
        if (g_is_null ead3 || length ead3 = 0) then None
        else Some (nn_as_seq h ead3)
      )
    }
  )

/// This lemma ensures the equivalence between the abstract
/// and low-level computationally model of `plaintext3` struct
let lemma_plaintext3_mem_to_plaintext3_equiv
  (#cs:supported_cipherSuite) (#auth_material:authentication_material)
  (h:HS.mem) (ptx3_mem:plaintext3_mem #cs #auth_material)
  : Lemma (requires is_valid_plaintext3_mem h ptx3_mem)
  (ensures (
    let ptx3 = plaintext3_mem_to_plaintext3 h ptx3_mem in
    match ptx3_mem with id_cred_i, sig_or_mac3, ead3 -> (
      (~((g_is_null ead3) \/ length ead3 = 0) <==> Some? ptx3.ead3)
      /\ Seq.equal ptx3.id_cred_i (as_seq h id_cred_i)
      /\ Seq.equal ptx3.sig_or_mac3 (as_seq h sig_or_mac3)
      /\ ((~(g_is_null ead3) /\ length ead3 > 0) ==> (
        let ead3_v = Some?.v ptx3.ead3 in
        let ead3_v:lbytes (Seq.length ead3_v) = ead3_v in
        Seq.equal ead3_v (nn_as_seq h ead3)
      ))
      /\ Spec.concat_ptx3_get_length ptx3 = size_v (plaintext3_mem_get_length ptx3_mem)
    )
  ))
  [SMTPat (plaintext3_mem_to_plaintext3 #cs #auth_material h ptx3_mem)]
  = let ptx3 = plaintext3_mem_to_plaintext3 h ptx3_mem in
  let ptx3_concat_len = Spec.concat_ptx3_get_length ptx3 in
  Spec.lemma_serialize_ptx3_get_length_concat_equiv ptx3;
  ()

inline_for_extraction
type concat_ptx3_st =
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> ptx3_mem:plaintext3_mem #cs #auth_material
  -> ptx3_buff:lbuffer uint8 (plaintext3_mem_get_length ptx3_mem)
  -> ST.Stack unit
  (requires fun h0 -> (
    is_valid_plaintext3_mem h0 ptx3_mem
    /\ live h0 ptx3_buff
    /\ plaintext3_mem_disjoint_to_buffer ptx3_mem ptx3_buff
  ))
  (ensures fun h0 _ h1 -> (
    lemma_plaintext3_mem_to_plaintext3_equiv h0 ptx3_mem;
    let ptx3_abstract = plaintext3_mem_to_plaintext3 h0 ptx3_mem in
    let ptx3_abstract_concat = Spec.serialize_ptx3 ptx3_abstract in
    let ptx3_abstract_concat:lbytes (Seq.length ptx3_abstract_concat)
      = ptx3_abstract_concat in
    assert(Seq.length ptx3_abstract_concat = length ptx3_buff);

    modifies1 ptx3_buff h0 h1
    /\ Seq.equal ptx3_abstract_concat (as_seq h1 ptx3_buff)
  ))

val concat_ptx3_mem: concat_ptx3_st

inline_for_extraction
let serialize_ptx3_mem
  :concat_ptx3_st
  = concat_ptx3_mem

val deserialize_ptx3_mem:
  #cs:supported_cipherSuite
  -> #auth_material:authentication_material
  -> #len_ptx3:size_t{len_ptx3 = plaintext3_len_fixed_v cs auth_material}
  -> #len_id_cred_i:size_t{size_v len_id_cred_i = Spec.id_cred_size}
  -> #len_sig_or_mac3:size_t{len_sig_or_mac3 = sig_or_mac23_size_v cs auth_material}
  -> serialized_ptx3_mem:lbuffer uint8 len_ptx3
  -> id_cred_i_buff:lbuffer uint8 len_id_cred_i
  -> sig_or_mac3_buff:lbuffer uint8 len_sig_or_mac3
  -> ead3_buff:ead_buff
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 serialized_ptx3_mem /\ live h0 id_cred_i_buff
    /\ live h0 sig_or_mac3_buff /\ live h0 ead3_buff
    /\ B.all_disjoint [loc serialized_ptx3_mem; loc id_cred_i_buff;
                      loc sig_or_mac3_buff; loc ead3_buff]
    /\ (
      let len_ead3 = length ead3_buff in

      length ead3_buff = Spec.ead_max_size
      /\ size_v (len_id_cred_i +! len_sig_or_mac3 +! (size len_ead3)) = size_v len_ptx3
    ) 
  ))
  (ensures fun h0 _ h1 -> (
    (g_is_null ead3_buff ==> modifies2 id_cred_i_buff sig_or_mac3_buff h0 h1)
    /\ (
      let (id_cred_i, sig_or_mac3, ead3)
        = Spec.deserialize_ptx3_raw_bytes #cs #auth_material (as_seq h0 serialized_ptx3_mem) in

      Seq.equal id_cred_i (as_seq h1 id_cred_i_buff)
      /\ Seq.equal sig_or_mac3 (as_seq h1 sig_or_mac3_buff)
      // no need to check EAD3 currently as EAD is not supported
      /\ (Some? ead3 /\ (Seq.length (Some?.v ead3) > 0) /\ ~(g_is_null ead3_buff) ==> (
        let ead3 = Some?.v ead3 in
        let ead3:lbytes (Seq.length ead3) = ead3 in

        modifies3 id_cred_i_buff sig_or_mac3_buff ead3_buff h0 h1
        /\ Seq.equal ead3 (nn_as_seq h1 ead3_buff)
      ))
    )
  ))