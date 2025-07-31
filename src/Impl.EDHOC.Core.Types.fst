module Impl.EDHOC.Core.Types


(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

module Spec = Spec.EDHOC.Core

let update_ps_mem_shared_key #cs src_keypair ps_m
  = match src_keypair with src_pub, src_priv -> (
    if (is_null src_priv) then ()
    else (
      if (is_null src_pub) then ()
      else
      let opt_shared_keypair = party_state_mem_get_shared_key ps_m in
      (**) let h0 = ST.get () in
      (**) assert(is_valid_opt_ec_keypair_mem h0 opt_shared_keypair);
      (**) assert(live h0 src_pub /\ live h0 src_priv);
      (**) assert((g_is_null src_pub <==> g_is_null src_priv));
      update_opt_ec_keypair_mem #cs opt_shared_keypair src_pub src_priv
    )
  )
  