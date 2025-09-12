module Impl.KEMEDHOC.Core.Msg1

(*HACL Random lib*)
open Lib.RandomBuffer.System

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

module FBytes = FStar.Bytes

(*Specification modules*)
module Spec = Spec.KEMEDHOC.Core
friend Spec.KEMEDHOC.Core

module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecParser = Spec.KEMEDHOC.Parser

module TypeEdhoc = TypeHelper.EDHOC
module SpecEdhocSerd = Spec.EDHOC.Serialization

#push-options "--z3rlimit 60 --max_fuel 4 --max_ifuel 4"
let initiator_send_msg1 kcs is msg1 hs
  = ST.push_frame();
  (**) let h0 = ST.get () in

  // generate connection ID C_I
  crypto_random msg1.c_i (size SpecParser.c_id_size);
  (**) let h1 = ST.get () in
  (**) assert(modifies (loc entropy_p |+| loc msg1.c_i) h0 h1);

  // generate ephemeral KEM key pair
  let pk_x = msg1.pk_x in
  let sk_x = is.eph_kem_priv_key.value in
  let sk_x_is_some = is.eph_kem_priv_key.is_some in
  (**) assert(disjoint pk_x sk_x);
  kem_keygen kcs pk_x sk_x;
  (**) let h2 = ST.get () in
  (**) assert(modifies (loc entropy_p |+| loc msg1.c_i
            |+| loc pk_x |+| loc sk_x |+| loc kem_state
  ) h0 h2);
  nat_to_bytes 1ul sk_x_is_some 1;
  (**) let h2_1 = ST.get () in
  (**) assert(modifies1 sk_x_is_some h2 h2_1);
  (**) assert(modifies (loc entropy_p |+| loc msg1.c_i
            |+| loc pk_x |+| loc sk_x |+| loc kem_state
            |+| loc sk_x_is_some
  ) h0 h2);

  // encap the Responder's static public KEM key for authentication
  let ct_auth_R = msg1.ct_auth_R in
  let k_auth_R = hs.k_auth_R in
  (**) assert(B.all_disjoint [loc is.remote_static_kem_pub_key; loc ct_auth_R; loc k_auth_R; loc entropy_p; loc kem_state]);
  kem_encaps kcs is.remote_static_kem_pub_key ct_auth_R k_auth_R;
  (**) let h3 = ST.get () in
  // (**) assert(modifies (loc entropy_p |+| loc kem_state |+| loc ct_auth_R
  //                     |+| loc k_auth_R) h0 h3);
  (**) assert(modifies (loc entropy_p |+| loc msg1.c_i
            |+| loc pk_x |+| loc sk_x |+| loc kem_state
            |+| loc sk_x_is_some
            |+| loc ct_auth_R |+| loc k_auth_R
  ) h0 h3);

  // compute TH1
  compute_th1 #kcs pk_x ct_auth_R hs.th1;
  (**) let h4 = ST.get () in
  (**) assert(modifies1 hs.th1 h3 h4);
  (**) assert( modifies (loc entropy_p |+| loc msg1.c_i
            |+| loc pk_x |+| loc sk_x |+| loc kem_state
            |+| loc sk_x_is_some
            |+| loc ct_auth_R |+| loc k_auth_R
            |+| loc hs.th1
  ) h0 h4);

  // derive PRK1e
  extract_prk1e #kcs hs.th1 k_auth_R hs.prk1e;
  (**) let h5 = ST.get () in
  (**) assert(modifies1 hs.prk1e h4 h5);
  (**) assert( modifies (loc entropy_p |+| loc msg1.c_i
            |+| loc pk_x |+| loc sk_x |+| loc kem_state
            |+| loc sk_x_is_some
            |+| loc ct_auth_R |+| loc k_auth_R
            |+| loc hs.th1
            |+| loc hs.prk1e
  ) h0 h5);

  // construct credential payload
  let cred_I = create (size SpecParser.cred_size) (u8 0) in
  copy cred_I is.id_cred;
  (**) let h6 = ST.get () in
  // (**) assert(modifies1 cred_I h5 h6);
  (**) assert(modifies (loc entropy_p |+| loc msg1.c_i
            |+| loc pk_x |+| loc sk_x |+| loc kem_state
            |+| loc sk_x_is_some
            |+| loc ct_auth_R |+| loc k_auth_R
            |+| loc hs.th1
            |+| loc hs.prk1e
            |+| loc cred_I)
  h0 h6);

  // construct plaintext1
  let p1 = construct_plaintext1 is.id_cred cred_I in
  let ptx1_concat_len = plaintext1_size_t in
  (**) assert(is_valid_plaintext1 h6 p1);

  // encrypt plaintext1 to ciphertext1
  let res = encrypt_plaintext1 #kcs p1 hs.th1 hs.prk1e msg1.c1 in
  (**) let h7 = ST.get () in
  (**) assert(match res with
    | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig | TypeEdhoc.CSuccess -> True
    | _ -> False  
  );

  let final_res = match res with
    | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> (
      (**) assert(modifies0 h6 h7);
      (**) assert(modifies (loc entropy_p |+| loc msg1.c_i
            |+| loc pk_x |+| loc sk_x |+| loc kem_state
            |+| loc sk_x_is_some
            |+| loc ct_auth_R |+| loc k_auth_R
            |+| loc hs.th1
            |+| loc hs.prk1e
            |+| loc cred_I
      ) h0 h7);
      res
    )
    | TypeEdhoc.CSuccess -> (
      (**) let hx = ST.get() in
      (**) assert(TypeEdhoc.CSuccess? res);
      // (**) assert(modifies1 msg1.c1 h6 h7);
      // construct message1
      // only need to update the method and suite_i fields
      (**) assert(live hx msg1.method /\ FBytes.repr_bytes 5 = 1);
      nat_to_bytes 1ul msg1.method 5;
      let suite_label = Some?.v (SpecCrypto.get_kemCipherSuite_label kcs) in
      (**) assert(live hx msg1.suite_i /\ FBytes.repr_bytes suite_label = 1);
      nat_to_bytes 1ul msg1.suite_i suite_label;
      (**) let h8 = ST.get () in
      (**) assert(
        SpecEdhocSerd.bytes_to_nat (as_seq h8 msg1.method) = 5
        /\ SpecEdhocSerd.bytes_to_nat (as_seq h8 msg1.suite_i) = Some?.v (SpecCrypto.get_kemCipherSuite_label kcs)
      );

      // compute hash of message1
      let msg1_concat_len = concat_msg1_fixed_length_t kcs in
      let msg1_concat_buffer = create msg1_concat_len (u8 0) in
      (**) assert(message1_disjoint_to_lbuffer msg1 msg1_concat_buffer);
      (**) assert(is_valid_message1 h8 msg1);
      concat_msg1 kcs msg1 msg1_concat_buffer;
      (**) let h9 = ST.get () in

      (**) assert(disjoint msg1_concat_buffer hs.msg1_hash);
      (**) assert(live h9 msg1_concat_buffer /\ live h9 hs.msg1_hash);
      do_hash kcs hs.msg1_hash msg1_concat_len msg1_concat_buffer;
      (**) let h10 = ST.get () in

      res 
    ) in

    ST.pop_frame();
    final_res

#pop-options