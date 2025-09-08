module Spec.KEMEDHOC.TranscriptHash

module EdhocCrypto = Spec.EDHOC.CryptoPrimitives
module Seq = Lib.Sequence

open Spec.EDHOC.Serialization

/// Transcript Hash 1
let compute_th1 #kcs pk_X ct_auth_R
  = do_hash kcs (pk_X @< ct_auth_R)

/// Transcript Hash 2
let compute_th2 #kcs ct_y k_auth_I msg1
  = let msg1_hash = do_hash kcs (concat_msg1 msg1) in
  let input_hash = (ct_y @< k_auth_I @< msg1_hash) in
  // let input_hash = Seq.concat (Seq.concat ct_y k_auth_I) msg1_hash in
  (**) assert(
    let concat_input_hash = Seq.concat (Seq.concat ct_y k_auth_I) msg1_hash in
    Seq.equal input_hash concat_input_hash
  );
  do_hash kcs input_hash

let compute_th2_pre_hash #kcs ct_y k_auth_I msg1_hash
  =
  // let input_hash = Seq.concat (Seq.concat ct_y k_auth_I) msg1_hash in
  let input_hash = (ct_y @< k_auth_I @< msg1_hash) in
  do_hash kcs input_hash

let lemma_compute_th2_equal_pre_hash #kcs ct_y k_auth_I msg1
  = ()

/// Transcript Hash 3
let compute_th3 #kcs th2 ptx2 cred_r
  = do_hash kcs (th2 @< (concat_ptx2 ptx2) @< cred_r)

/// Transcript Hash 4
let compute_th4 #kcs th3 ptx3 cred_i
  = do_hash kcs (th3 @< (concat_ptx3 ptx3) @< cred_i)