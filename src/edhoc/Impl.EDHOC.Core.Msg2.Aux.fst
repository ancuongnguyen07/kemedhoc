module Impl.EDHOC.Core.Msg2.Aux

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence
module BSeq = Lib.ByteSequence

// friend Spec.EDHOC.Core.Lemmas

module Spec = Spec.EDHOC.Core
module SpecParser = Spec.EDHOC.Parser
module SpecDef = Spec.EDHOC.Base.Definitions
module SpecKS = Spec.EDHOC.KeySchedule
module SpecCrypto = Spec.EDHOC.CryptoPrimitives

open Spec.EDHOC.Serialization

friend Spec.EDHOC.Core

#push-options "--z3rlimit 10 --max_fuel 8 --max_ifuel 8"

let verify_sig_or_mac2 #cs auth_material sig_or_mac2_m mac2_m context2_m pk_r_m
  = let hinit = ST.get () in
  let id_cred_r_m = context2_mem_get_id_cred_r context2_m in
  let cred_r_m = context2_mem_get_cred_r context2_m in
  let th2_m = context2_mem_get_th2 context2_m in
  let ead2_m = context2_mem_get_ead2 context2_m in

  let mac2_len = mac23_size_v cs auth_material in
  (**) assert(length mac2_m = size_v mac2_len);

  match auth_material with
      | SpecCrypto.Signature -> (
        assert(length sig_or_mac2_m = SpecCrypto.signature_size);
        assert(~(g_is_null pk_r_m));

        /// Push frame!!!
        ST.push_frame();
        
        let res = match (is_null ead2_m) with
          | true -> (
            /// There is NO EAD2

            let tbv_len = size (SpecParser.id_cred_size
                    + (SpecCrypto.hash_size cs) + SpecParser.cred_size) +! mac2_len in

            let tbv_m = create (tbv_len) (u8 0) in
            concat_buff4 id_cred_r_m th2_m cred_r_m mac2_m tbv_m;
            (**) let h1 = ST.get () in
            (**) assert(
              let c2 = context2_mem_to_context2 hinit context2_m in
              let mac2 = as_seq hinit mac2_m in

              modifies1 tbv_m hinit h1
              /\ Seq.equal (as_seq h1 tbv_m) (c2.id_cred_r @< c2.th2 @< c2.cred_r @< mac2)
            );


            ecdsa_verify cs tbv_len tbv_m pk_r_m sig_or_mac2_m
          )
          | false -> (
            /// There is EAD2

            let tbv_len = size (SpecParser.id_cred_size + SpecParser.ead_max_size
                    + (SpecCrypto.hash_size cs) + SpecParser.cred_size) +! mac2_len in

            let tbv_m = create (tbv_len) (u8 0) in
            concat_buff5 id_cred_r_m th2_m cred_r_m (ead2_m <: lbuffer uint8 (size SpecParser.ead_max_size))
                mac2_m tbv_m;
            (**) let h1 = ST.get () in
            (**) assert(
              let c2 = context2_mem_to_context2 hinit context2_m in
              let mac2 = as_seq hinit mac2_m in
              let ead2_v = Some?.v c2.ead2 in
              let ead2_v:BSeq.lbytes (Seq.length ead2_v) = ead2_v in

              modifies1 tbv_m hinit h1
              /\ Seq.equal (as_seq h1 tbv_m) (c2.id_cred_r @< c2.th2 @< c2.cred_r @< ead2_v @< mac2)
            );

            ecdsa_verify cs tbv_len tbv_m pk_r_m sig_or_mac2_m
          ) in

          ST.pop_frame();
          res
      )
      | SpecCrypto.MAC -> (
        assert(length sig_or_mac2_m = size_v (mac23_size_v cs auth_material));
        lbytes_eq mac2_m sig_or_mac2_m
      )

let derive_sig_or_mac2 #cs auth_material sk_r_m mac2_m context2_m sig_or_mac2_m
  = let hinit = ST.get () in
  let id_cred_r = context2_mem_get_id_cred_r context2_m in
  let cred_r = context2_mem_get_cred_r context2_m in
  let th2 = context2_mem_get_th2 context2_m in
  let ead2 = context2_mem_get_ead2 context2_m in

  let mac2_len = mac23_size_v cs auth_material in
  (**) assert(size_v mac2_len = length mac2_m);

  match auth_material with
    | SpecCrypto.MAC -> (
      assert(length sig_or_mac2_m = length mac2_m);
      copy sig_or_mac2_m mac2_m;
      (**) let h1 = ST.get () in
      (**) assert(
        modifies1 sig_or_mac2_m hinit h1 /\
        Seq.equal (as_seq hinit mac2_m) (as_seq h1 sig_or_mac2_m)
      );

      CSuccess
    )
    | SpecCrypto.Signature -> (
      (**) assert(~(g_is_null sk_r_m));
      let return_code = match (is_null ead2) with
        | true -> (
        /// Push frame!!!
        ST.push_frame();
        let tbs_len = size (SpecParser.id_cred_size
                + (SpecCrypto.hash_size cs) + SpecParser.cred_size) +! mac2_len in
        let to_be_signed_m = create tbs_len (u8 0) in
        // concat to_be_signed
        concat_buff4 id_cred_r th2 cred_r mac2_m to_be_signed_m;
        (**) let h1 = ST.get () in
        (**) assert(
          let c2 = context2_mem_to_context2 hinit context2_m in
          let mac2 = as_seq hinit mac2_m in
          Seq.equal (as_seq h1 to_be_signed_m) (c2.id_cred_r @< c2.th2 @< c2.cred_r @< mac2)
        );

        let nonce = create 32ul (u8 0) in
        crypto_random nonce 32ul;

        let res = ecdsa_sign cs sig_or_mac2_m (Some nonce) tbs_len to_be_signed_m sk_r_m in
        /// Pop frame!!!!
        ST.pop_frame();
        res
      )
        | false -> (
        /// Push frame!!!
        ST.push_frame();
        let tbs_len = size (SpecParser.id_cred_size + SpecParser.ead_max_size
                + (SpecCrypto.hash_size cs) + SpecParser.cred_size) +! mac2_len in
        let to_be_signed_m = create tbs_len (u8 0) in
        // concat to_be_signed
        concat_buff5 id_cred_r th2 cred_r (ead2 <: lbuffer uint8 (size SpecParser.ead_max_size))
          mac2_m to_be_signed_m;
        (**) let h1 = ST.get () in
        (**) assert(
          let c2 = context2_mem_to_context2 hinit context2_m in
          let mac2 = as_seq hinit mac2_m in
          let ead2_v = Some?.v c2.ead2 in
          let ead2_v:BSeq.lbytes (Seq.length ead2_v) = ead2_v in

          Seq.equal (as_seq h1 to_be_signed_m) (c2.id_cred_r @< c2.th2 @< c2.cred_r
                    @< ead2_v @< mac2)
        );

        let nonce = create 32ul (u8 0) in
        crypto_random nonce 32ul;

        let res = ecdsa_sign cs sig_or_mac2_m (Some nonce) tbs_len to_be_signed_m sk_r_m in

        /// Pop frame!!!
        ST.pop_frame();

        res
      ) in

      if (return_code) then CSuccess
      else CInvalidECPoint
    )

  


let derive_prk3e2m #cs auth_material prk2e_m th2_m r_m pub_m prk3e2m_m
  = let hinit = ST.get () in
  match (auth_material) with
    | SpecCrypto.Signature -> (
      // If the signature is used then PRK3e2m = PRK2e
      copy prk3e2m_m prk2e_m;
      (**) let h1 = ST.get () in
      (**) assert(modifies1 prk3e2m_m hinit h1);
      CSuccess
    )
    | SpecCrypto.MAC -> (
      // get ephemeral-static DH share for implicit authentication
      
      /// Push frame!!!
      ST.push_frame();

      let ss_m = create (shared_secret_size_v cs) (u8 0) in

      let res_dh = dh ss_m r_m pub_m in
      if (res_dh)
      then (
        // derive SALT3e2m
        (**) let h1 = ST.get () in
        (**) assert(
          let r = nn_as_seq hinit r_m in
          let g_x = nn_as_seq hinit pub_m in

          let res_grx = SpecCrypto.dh #cs r g_x in

          (Some? res_grx <==> res_dh) /\
          (Some? res_grx ==> Seq.equal (as_seq h1 ss_m) (Some?.v res_grx))
        );

        let salt3e2m_m = create (size (SpecCrypto.hash_size cs)) (u8 0) in
        expand_salt3e2m prk2e_m th2_m salt3e2m_m;
        (**) let h2 = ST.get () in
        (**) assert(
          let prk2e = as_seq hinit prk2e_m in
          let th2 = as_seq hinit th2_m in

          let salt = SpecKS.expand_salt3e2m #cs prk2e th2 in
          Seq.equal (as_seq h2 salt3e2m_m) salt 
        );

        // extract PRK3e2m
        extract_prk3e2m salt3e2m_m ss_m prk3e2m_m;

        /// Pop frame!!!
        ST.pop_frame();
        
        CSuccess
      )
      else (
        /// Pop frame!!!
        ST.pop_frame();

        CInvalidECPoint
      )
    )

#pop-options