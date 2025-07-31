# Issues

### Msg1-Msg3 integration proofs

Although I have admitted the lemma that ephemeral-static DH sharing
is functionally correct. There is still a gap in desrializing
`msg3` as an encryption of `plaintext3`
```
initiator_send_msg3 (is:party_state_shared_est #cs)
 (hs:handshake_state_after_msg2 #cs):
	let g_y = Some?.v hs.g_y in
	let i = is.static_dh.priv in

responder_process_msg3 (rs:party_state_shared_est #cs)
 (hs:handshake_state_after_msg2 #cs):
	let y = (Some?.v rs.eph_ec_keypair).priv in
	let g_i = rs.remote_static_pub_key in
```
