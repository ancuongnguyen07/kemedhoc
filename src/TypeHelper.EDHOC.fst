module TypeHelper.EDHOC

let update_opt_ec_keypair_mem #cs kp_m pub_buff priv_buff
  =
  (**) let h0 = ST.get () in
  if is_null priv_buff then ()
  else (
    match kp_m with opt_pub, opt_priv -> (
      update_sub (opt_pub <: ec_pub_key_buf cs) 0ul (pub_key_size_v cs)
        (pub_buff <: ec_pub_key_buf cs);
      update_sub (opt_priv <: ec_priv_key_buf cs) 0ul (priv_key_size_v cs)
        (priv_buff <: ec_priv_key_buf cs)
    )
  )
