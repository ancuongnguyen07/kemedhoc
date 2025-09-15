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

#push-options "--z3rlimit 40 --max_fuel 4 --max_ifuel 4"
let responder_process_msg1 kcs rs msg1 hs
  = (**) let h0 = ST.get () in
  ST.push_frame();

  // decap ct_auth_R -> get K_auth_R
  let sk_R = get_priv_kem_key_m rs.static_kem_kp in
  (**) assert(live h0 sk_R
    /\ live h0 msg1.ct_auth_R
    /\ live h0 hs.k_auth_R);
  kem_decaps kcs sk_R msg1.ct_auth_R hs.k_auth_R;
  (**) let h1 = ST.get () in
  (**) assert(modifies1 hs.k_auth_R h0 h1);

  // derive TH1
  compute_th1 #kcs msg1.pk_x msg1.ct_auth_R hs.th1;
  (**) let h2 = ST.get () in
  (**) assert(modifies (loc hs.k_auth_R |+| loc hs.th1) h0 h2);

  // derive PRK1e
  extract_prk1e #kcs hs.th1 hs.k_auth_R hs.prk1e;
  (**) let h3 = ST.get () in
  (**) assert(modifies1 hs.prk1e h2 h3);
  // (**) assert(modifies (loc hs.k_auth_R |+| loc hs.th1 |+| loc hs.prk1e) h0 h3);

  // decrypt ciphertext1 -> get plaintext1
  // let ptx1_buffer = create (plaintext1_size_t kcs) (u8 0) in
  // let res = decrypt_ciphertext1 #kcs msg1.c1 hs.th1 hs.prk1e ptx1_buffer in
  // let final_res = match res with
  //   | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig
  //   | TypeEdhoc.CDecryptionFailure -> res
  //   | TypeEdhoc.CSuccess -> (
  //     // compute hash of message1
  //     let msg1_concat_len = concat_msg1_fixed_length_t kcs in
  //     let msg1_concat_buffer = create msg1_concat_len (u8 0) in
  //     (**) assert(message1_disjoint_to_lbuffer msg1 msg1_concat_buffer);
  //     do_hash kcs hs.msg1_hash msg1_concat_len msg1_concat_buffer;
  //     (**) let h5 = ST.get () in
  //     (**) assert(modifies (loc hs.k_auth_R |+| loc hs.th1 |+| loc hs.prk1e
  //           |+| loc ptx1_buffer
  //           |+| loc hs.msg1_hash
  //     ) h0 h5);

  //     res

  //   ) in

  ST.pop_frame();
  TypeEdhoc.CSuccess

#pop-options


/// Initiator's side
#push-options "--z3rlimit 40 --max_fuel 4 --max_ifuel 4"
let initiator_set_up_msg1 kcs is hs msg1
  = (**) let h0 = ST.get () in

  // generate connection ID C_I
  crypto_random msg1.c_i (size SpecParser.c_id_size);
  (**) let h1 = ST.get () in
  (**) assert(modifies (loc entropy_p |+| loc msg1.c_i) h0 h1);

  // generate ephemeral KEM key pair
  let pk_x = msg1.pk_x in
  let sk_x = is.eph_kem_priv_key.value in
  (**) assert(disjoint pk_x sk_x);
  kem_keygen kcs pk_x sk_x;
  (**) let h2 = ST.get () in
  (**) assert(modifies (loc entropy_p |+| loc msg1.c_i
            |+| loc pk_x |+| loc sk_x |+| loc kem_state
  ) h0 h2);
  lbufferOpt_set_Some is.eph_kem_priv_key;
  let sk_x_is_some = is.eph_kem_priv_key.is_some in
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
  ) h0 h5)

let initiator_construct_msg1_uti
  (kcs: supportedKemCipherSuite) (mode: TypeEdhoc.c_response)
  (is: party_state_m kcs) (hs: handshake_state_m kcs)
  (msg1: message1 kcs)
  : ST.Stack c_response
  (requires fun h0 -> (mode == TypeEdhoc.CSuccess 
  \/ mode == TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig)
    /\ is_valid_handshake_state_m h0 hs
    /\ is_valid_party_state_m h0 is
    /\ is_valid_message1 h0 msg1

    // Disjointness
    /\ handshake_state_m_disjoint_to_party_state hs is
    /\ handshake_state_m_disjoint_to_msg1 hs msg1
    /\ party_state_disjoint_to_msg1 is msg1
  )
  (ensures fun h0 res h1 ->
    res == mode
    /\ (match res with
      | TypeEdhoc.CSuccess -> (
        let modified_locs = loc msg1.method |+| loc msg1.suite_i
                |+| loc hs.msg1_hash in

        modifies modified_locs h0 h1
        /\ is_valid_handshake_state_m h1 hs
        /\ is_valid_party_state_m h1 is
        /\ is_valid_message1 h1 msg1 /\ is_legit_message1 h1 msg1
      )
      | TypeEdhoc.CUnsupportedAlgorithmOrInvalidConfig -> modifies0 h0 h1
    )
  )
  = match mode with
    | TypeEdhoc.CSuccess -> (
      ST.push_frame();
      (**) let h0 = ST.get () in

      // construct message1
      // only need to update the method and suite_i fields
      (**) assert(live h0 msg1.method /\ FBytes.repr_bytes 5 = 1);
      nat_to_bytes 1ul msg1.method 5;
      let suite_label = Some?.v (SpecCrypto.get_kemCipherSuite_label kcs) in
      (**) assert(suite_label = 9);
      (**) assert(live h0 msg1.suite_i /\ FBytes.repr_bytes suite_label = 1);
      nat_to_bytes 1ul msg1.suite_i suite_label;
      (**) let h8 = ST.get () in
      (**) assert(
        SpecEdhocSerd.bytes_to_nat (as_seq h8 msg1.method) = 5
        /\ SpecEdhocSerd.bytes_to_nat (as_seq h8 msg1.suite_i) = suite_label
      );
      // (**) assert(modifies (loc cred_I
      //       |+| loc msg1.c1
      //       |+| loc msg1.method |+| loc msg1.suite_i
      // ) h0 h8);

      // compute hash of message1
      let msg1_concat_len = concat_msg1_fixed_length_t kcs in
      let msg1_concat_buffer = create msg1_concat_len (u8 0) in
      (**) assert(message1_disjoint_to_lbuffer msg1 msg1_concat_buffer);
      (**) assert(is_valid_message1 h8 msg1 /\ is_legit_message1 h8 msg1);
      concat_msg1 kcs msg1 msg1_concat_buffer;
      (**) let h9 = ST.get () in
      // (**) assert(modifies (loc cred_I
      //       |+| loc msg1.c1
      //       |+| loc msg1.method |+| loc msg1.suite_i
      //       |+| loc msg1_concat_buffer
      // ) h0 h9);

      (**) assert(disjoint msg1_concat_buffer hs.msg1_hash);
      (**) assert(live h9 msg1_concat_buffer /\ live h9 hs.msg1_hash);
      do_hash kcs hs.msg1_hash msg1_concat_len msg1_concat_buffer;
      (**) let h10 = ST.get () in
      // (**) assert(modifies (loc cred_I
      //       |+| loc msg1.c1
      //       |+| loc msg1.method |+| loc msg1.suite_i
      //       |+| loc msg1_concat_buffer
      //       |+| loc hs.msg1_hash
      // ) h0 h10);

      (**) assert(
        (
          is_valid_handshake_state_m h10 hs
          /\ is_valid_party_state_m h10 is
          /\ is_valid_message1 h10 msg1 /\ is_legit_message1 h10 msg1
        )
      );

      ST.pop_frame();
      (**) let h_final = ST.get () in
      (**) assert(
        (
          is_valid_handshake_state_m h_final hs
          /\ is_valid_party_state_m h_final is
          /\ is_valid_message1 h_final msg1 /\ is_legit_message1 h_final msg1
        )
      );
      mode
    )
    | _ -> mode
#pop-options

#push-options "--z3refresh --z3rlimit 40 --max_fuel 4 --max_ifuel 4"
let initiator_construct_msg1 kcs is hs msg1
  = ST.push_frame();
  (**) let h0 = ST.get () in

  // construct credential payload
  let cred_I = create (size SpecParser.cred_size) (u8 0) in
  copy cred_I is.id_cred;
  (**) let h6 = ST.get () in

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

  let final_res = initiator_construct_msg1_uti kcs res is hs msg1 in
  ST.pop_frame();
    
  final_res

#pop-options


#push-options "--z3refresh --z3rlimit 50 --max_fuel 4 --max_ifuel 4"
let initiator_send_msg1 kcs is msg1 hs
  = (**) let h0 = ST.get () in
  ST.push_frame();

  initiator_set_up_msg1 kcs is hs msg1;
  let final_res = initiator_construct_msg1 kcs is hs msg1 in

  ST.pop_frame();
  (**) let h_final = ST.get () in
  (**) assert( final_res == TypeEdhoc.CSuccess ==> (
    is_valid_handshake_state_m h_final hs
    /\ is_valid_party_state_m h_final is
    /\ is_valid_message1 h_final msg1 /\ is_legit_message1 h_final msg1)
  );
  assume(
    let is_init = party_state_m_eval h0 is in
    let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased HACLRandom.entropy)) in

    match (Spec.initiator_send_msg1 kcs is_init e0_v) with
      | Fail _ -> False
      | Res (msg1_spec, is_spec, hs_spec) -> (
        final_res == TypeEdhoc.CSuccess ==> (
          Spec.hs_equal (handshake_state_m_eval h_final hs) hs_spec
          /\ Spec.ps_equal_all (party_state_m_eval h_final is) is_spec
          /\ SpecParser.message1_equal (message1_eval h_final msg1) msg1_spec
        )
      )
  );
  final_res

#pop-options