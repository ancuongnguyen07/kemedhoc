module Spec.EDHOC.TranscriptHash

open Lib.ByteSequence
open Lib.Sequence

// open Spec.EDHOC.Base.Definitions
// open Spec.EDHOC.CryptoPrimitives
// open Spec.EDHOC.Parser
open Spec.EDHOC.Serialization

/// Transcript Hash 2
let compute_th2 #cs msg1 g_y
  = let msg1_hash = do_hash cs (concat_msg1 msg1) in
  // let g_y_lbytes:lbytes (length g_y) = g_y in
  do_hash cs (msg1_hash @< g_y)

let compute_th2_pre_hash #cs msg1_hash g_y
  = do_hash cs (msg1_hash @< g_y)

/// Transcript Hash 3
let compute_th3 #cs #auth_material th2 ptx2 cred_r
  = let ptx2_lbytes = concat_ptx2 ptx2 in
  let cred_r_lbytes:lbytes (length cred_r) = cred_r in
  (do_hash cs (th2 @< ptx2_lbytes @< cred_r_lbytes))
 
/// Transcript Hash 4
let compute_th4 #cs #auth_material th3 ptx3 cred_i
  = let ptx3_lbytes = concat_ptx3 ptx3 in
  let cred_i_lbytes:lbytes (length cred_i) = cred_i in
  let temp = th3 @< ptx3_lbytes in
  (do_hash cs (th3 @< ptx3_lbytes @< cred_i_lbytes))
