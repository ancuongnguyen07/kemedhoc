module Impl.EDHOC.Parser

(*LowStar modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence
module Buffer = Lib.Buffer

friend Spec.EDHOC.KeySchedule

/// -----------------------------
/// HKDF Info
/// -----------------------------

let concat_info_mem context_len okm_len_byte_len i_mem info_buff
  = match i_mem with label_buff, context_buff, okm_len_buff -> (
    concat_buff3 #MUT #uint8 #1ul #context_len #okm_len_byte_len
      label_buff context_buff okm_len_buff info_buff
  )

/// -----------------------------
/// Context 2
/// -----------------------------

let concat_context2_mem #cs context2 context2_buff
  = match context2 with c_r_buff, id_cred_r_buff, th2_buff, cred_r_buff, ead2_buff -> (
    if is_null ead2_buff
    then concat_buff4 c_r_buff id_cred_r_buff th2_buff cred_r_buff context2_buff
    else concat_buff5 c_r_buff id_cred_r_buff th2_buff cred_r_buff
        (ead2_buff <: lbuffer uint8 (size Spec.ead_max_size)) context2_buff
  )

/// -----------------------------
/// Context 3
/// -----------------------------

let concat_context3_mem #cs context3 context3_buff
  = match context3 with id_cred_i_buff, th3_buff, cred_i_buff, ead3_buff -> (
    if is_null ead3_buff
    then concat_buff3 id_cred_i_buff th3_buff cred_i_buff context3_buff
    else concat_buff4 id_cred_i_buff th3_buff cred_i_buff
      (ead3_buff <: lbuffer uint8 (size Spec.ead_max_size)) context3_buff
  )

/// -----------------------------
/// Message 1
/// -----------------------------

let concat_msg1_mem #cs msg1 msg1_buff
  = let hinit = ST.get () in
  let method = message1_mem_get_method msg1 in
  let suite = message1_mem_get_suite_i msg1 in
  let g_x = message1_mem_get_g_x msg1 in
  let c_i = message1_mem_get_c_i msg1 in
  let ead1 = message1_mem_get_ead1 msg1 in
  let h0 = ST.get () in
  
  if is_null ead1
  then concat_buff4 method suite g_x c_i msg1_buff
  else concat_buff5 method suite g_x c_i
    (ead1 <: lbuffer uint8 (size Spec.ead_max_size)) msg1_buff
 
    
/// -----------------------------
/// Plaintext 2
/// -----------------------------

let concat_ptx2_mem #cs #auth_material #ptx2_len ptx2 ptx2_buff
  =
  let c_r = plaintext2_mem_get_c_r ptx2 in
  let id_cred_r = plaintext2_mem_get_id_cred_r ptx2 in
  let sig_or_mac2:lbuffer uint8 (size (Spec.sig_or_mac23_size cs auth_material))
    = plaintext2_mem_get_sig_or_mac2 ptx2 in
  let ead2 = plaintext2_mem_get_ead2 ptx2 in

  if is_null ead2
  then concat_buff3 c_r id_cred_r sig_or_mac2 ptx2_buff
  else concat_buff4 c_r id_cred_r sig_or_mac2
    (ead2 <: lbuffer uint8 (size Spec.ead_max_size)) ptx2_buff


let deserialize_ptx2_mem cs auth_material
  serialized_ptx2_mem c_r_buff id_cred_r_buff sig_or_mac2_buff ead2_buff
  = let h0 = ST.get () in
  let len_c_r = size (Spec.c_id_size) in
  let len_id_cred_r = size Spec.id_cred_size in
  let len_sig_or_mac2 = size (Spec.sig_or_mac23_size cs auth_material) in
  let len_ptx2 = plaintext2_len_fixed_v cs auth_material in
  let len_ead2 = size (Spec.ead_max_size) in

  let sub_c_r = (Buffer.sub serialized_ptx2_mem 0ul len_c_r) in
  copy c_r_buff sub_c_r;
  (**) let h1 = ST.get () in
  (**) assert(
    let p2 = as_seq h0 serialized_ptx2_mem in
    let c_r = Seq.sub p2 0 Spec.c_id_size in

    modifies1 c_r_buff h0 h1
    /\ Seq.equal c_r (as_seq h1 c_r_buff)
  );

  copy id_cred_r_buff (Buffer.sub serialized_ptx2_mem len_c_r len_id_cred_r);
  (**) let h2 = ST.get () in
  (**) assert(
    let p2 = as_seq h0 serialized_ptx2_mem in
    let id_cred_r = Seq.sub p2 Spec.c_id_size Spec.id_cred_size in

    modifies1 id_cred_r_buff h1 h2
    /\ Seq.equal id_cred_r (as_seq h2 id_cred_r_buff)
  );

  copy sig_or_mac2_buff
    (Buffer.sub  serialized_ptx2_mem (len_c_r +! len_id_cred_r) (len_sig_or_mac2));
  /// A place holder for deserializing EAD as
  /// this implementation does not support variant-length EAD currently
  if (size_v (len_c_r +! len_id_cred_r +! len_sig_or_mac2) < size_v len_ptx2) then
    if (not (is_null ead2_buff)) then
      let start = (len_c_r +! len_id_cred_r +! len_sig_or_mac2) in
      copy (ead2_buff <: lbuffer uint8 (size Spec.ead_max_size))
        (Buffer.sub serialized_ptx2_mem start len_ead2)
    else ()
  else
  let h1 = ST.get () in
  ()

/// -----------------------------
/// Message 2
/// -----------------------------

let concat_msg2_mem #cs #auth_material msg2_mem msg2_buff
  = let h0 = ST.get () in
  // NOTE! `ciphertext2_buff` is a defined type name
  // so DO NOT reuse this name
  match msg2_mem with | g_y, c2 -> (
    concat_buff2 g_y c2 msg2_buff
  )

/// -----------------------------
/// Plaintext 3
/// -----------------------------

let concat_ptx3_mem #cs #auth_material ptx3_mem ptx3_buff
  = match ptx3_mem with id_cred_i, sig_or_mac3, ead3 -> (
    if is_null ead3
    then concat_buff2 id_cred_i sig_or_mac3 ptx3_buff
    else concat_buff3 id_cred_i sig_or_mac3
      (ead3 <: lbuffer uint8 (size (Spec.ead_max_size))) ptx3_buff
  )

let deserialize_ptx3_mem #cs #auth_material #len_ptx3 #len_id_cred_i #len_sig_or_mac3
  serialized_ptx3_mem id_cred_i_buff sig_or_mac3_buff ead3_buff
  = let h0 = ST.get () in
  copy id_cred_i_buff (Buffer.sub serialized_ptx3_mem 0ul len_id_cred_i);

  copy sig_or_mac3_buff
    (Buffer.sub  serialized_ptx3_mem (len_id_cred_i) (len_sig_or_mac3));
  /// A place holder for deserializing EAD as
  /// this implementation does not support variant-length EAD currently
  if (size_v (len_id_cred_i +! len_sig_or_mac3) < size_v len_ptx3) then
    if (not (is_null ead3_buff)) then
      let start = (len_id_cred_i +! len_sig_or_mac3) in
      let len_ead3 = size Spec.ead_max_size in
      copy (ead3_buff <: lbuffer uint8 (size Spec.ead_max_size))
        (Buffer.sub serialized_ptx3_mem start len_ead3)
    else ()
  else
  let h1 = ST.get () in
  ()