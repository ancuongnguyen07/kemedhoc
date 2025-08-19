module Impl.EDHOC.Core.Msg3.Aux

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence
module BSeq = Lib.ByteSequence


module Spec = Spec.EDHOC.Core
module SpecParser = Spec.EDHOC.Parser
module SpecDef = Spec.EDHOC.Base.Definitions
module SpecKS = Spec.EDHOC.KeySchedule
module SpecCrypto = Spec.EDHOC.CryptoPrimitives

open Spec.EDHOC.Serialization

friend Spec.EDHOC.Core

(*-------------------------------------------*)
(*---------------------------- Responder side*)
(*-------------------------------------------*)
/// verify Sig_or_MAC3
let verify_sig_or_mac3 #cs auth_material sig_or_mac3_m mac3_m context3_m pk_i_m
  = let hinit = ST.get () in
  let id_cred_i_m = context3_mem_get_id_cred_i context3_m in
  let cred_i_m = context3_mem_get_cred_i context3_m in
  let th3_m = context3_mem_get_th3 context3_m in
  let ead3_m = context3_mem_get_ead3 context3_m in

  let mac3_len = mac23_size_v cs auth_material in
  (**) assert(length mac3_m = size_v mac3_len);

  match auth_material with
    | SpecCrypto.Signature -> (
      assert(length sig_or_mac3_m = SpecCrypto.signature_size);
      assert(~(g_is_null pk_i_m));

      /// Push frame!!!
      ST.push_frame();

      let res = match (is_null ead3_m) with
        | true -> (
          /// There is NO EAD3

          let tbv_len = size (SpecParser.id_cred_size
                    + (SpecCrypto.hash_size cs) + SpecParser.cred_size) +! mac3_len in

          let tbv_m = create (tbv_len) (u8 0) in
            concat_buff4 id_cred_i_m th3_m cred_i_m mac3_m tbv_m;
            (**) let h1 = ST.get () in
            (**) assert(
              let c3 = context3_mem_to_context3 hinit context3_m in
              let mac3 = as_seq hinit mac3_m in

              modifies1 tbv_m hinit h1
              /\ Seq.equal (as_seq h1 tbv_m) (c3.id_cred_i @< c3.th3 @< c3.cred_i @< mac3)
            );


            ecdsa_verify cs tbv_len tbv_m pk_i_m sig_or_mac3_m
        )
        | false -> (
          /// There is EAD3

          let tbv_len = size (SpecParser.id_cred_size + SpecParser.ead_max_size
                    + (SpecCrypto.hash_size cs) + SpecParser.cred_size) +! mac3_len in

          let tbv_m = create (tbv_len) (u8 0) in
          concat_buff5 id_cred_i_m th3_m cred_i_m (ead3_m <: lbuffer uint8 (size SpecParser.ead_max_size))
              mac3_m tbv_m;
          (**) let h1 = ST.get () in
          (**) assert(
            let c3 = context3_mem_to_context3 hinit context3_m in
            let mac3 = as_seq hinit mac3_m in
            let ead3_v = Some?.v c3.ead3 in
            let ead3_v:BSeq.lbytes (Seq.length ead3_v) = ead3_v in

            modifies1 tbv_m hinit h1
            /\ Seq.equal (as_seq h1 tbv_m) (c3.id_cred_i @< c3.th3 @< c3.cred_i @< ead3_v @< mac3)
          );


          ecdsa_verify cs tbv_len tbv_m pk_i_m sig_or_mac3_m
        ) in

        ST.pop_frame();
        res
    )
    | SpecCrypto.MAC -> (
      (**) assert(length sig_or_mac3_m = size_v (mac23_size_v cs auth_material));
      lbytes_eq mac3_m sig_or_mac3_m
    )


(*-------------------------------------------*)
(*---------------------------- Initiator side*)
(*-------------------------------------------*)

/// derive Sig_or_MAC3
let derive_sig_or_mac3 #cs auth_material sk_i_m mac3_m context3_m sig_or_mac3_m
  = let hinit = ST.get () in
  let id_cred_i = context3_mem_get_id_cred_i context3_m in
  let cred_i = context3_mem_get_cred_i context3_m in
  let th3 = context3_mem_get_th3 context3_m in
  let ead3 = context3_mem_get_ead3 context3_m in

  let mac3_len = mac23_size_v cs auth_material in
  (**) assert(size_v mac3_len = length mac3_m);

  match auth_material with
    | SpecCrypto.MAC -> (
      (**) assert(length sig_or_mac3_m = length mac3_m);
      copy sig_or_mac3_m mac3_m;

      CSuccess
    )
    | SpecCrypto.Signature -> (
      (**) assert(~(g_is_null sk_i_m));
      ST.push_frame();
      let return_code = match (is_null ead3) with
        | true -> (
          let tbs_len = size (SpecParser.id_cred_size
                  + (SpecCrypto.hash_size cs) + SpecParser.cred_size) +! mac3_len in
          let to_be_signed_m = create tbs_len (u8 0) in
          // concat to_be_signed
          concat_buff4 id_cred_i th3 cred_i mac3_m to_be_signed_m;
          (**) let h1 = ST.get () in
          (**) assert(
            let c3 = context3_mem_to_context3 hinit context3_m in
            let mac3 = as_seq hinit mac3_m in
            Seq.equal (as_seq h1 to_be_signed_m) (c3.id_cred_i @< c3.th3 @< c3.cred_i @< mac3)
          );

          let nonce = create 32ul (u8 0) in
          crypto_random nonce 32ul;

          ecdsa_sign cs sig_or_mac3_m (Some nonce) tbs_len to_be_signed_m sk_i_m
        )
        | false -> (
          let tbs_len = size (SpecParser.id_cred_size + SpecParser.ead_max_size
                  + (SpecCrypto.hash_size cs) + SpecParser.cred_size) +! mac3_len in
          let to_be_signed_m = create tbs_len (u8 0) in
          // concat to_be_signed
          concat_buff5 id_cred_i th3 cred_i (ead3 <: lbuffer uint8 (size SpecParser.ead_max_size))
              mac3_m to_be_signed_m;
          (**) let h1 = ST.get () in
          (**) assert(
            let c3 = context3_mem_to_context3 hinit context3_m in
            let mac3 = as_seq hinit mac3_m in
            let ead3_v = Some?.v c3.ead3 in
            let ead3_v:BSeq.lbytes (Seq.length ead3_v) = ead3_v in

            Seq.equal (as_seq h1 to_be_signed_m) (c3.id_cred_i @< c3.th3 @< c3.cred_i @< ead3_v @< mac3)
          );

          let nonce = create 32ul (u8 0) in
          crypto_random nonce 32ul;

          ecdsa_sign cs sig_or_mac3_m (Some nonce) tbs_len to_be_signed_m sk_i_m
        ) in

      ST.pop_frame();

      if (return_code) then CSuccess
      else CInvalidECPoint
    )

/// Intermediate: derive PRK4e3m for Initiator
let derive_prk4e3m #cs i_auth prk3e2m_m th3_m i_m pub_m prk4e3m_m
  = let hinit = ST.get() in
  match i_auth with
    | SpecCrypto.Signature -> (
      copy prk4e3m_m prk3e2m_m;

      CSuccess
    )
    | SpecCrypto.MAC -> (
      /// Push frame!!!
      ST.push_frame();

      let ss_m = create (shared_secret_size_v cs) (u8 0) in

      let res_dh = dh ss_m i_m pub_m in
      if (res_dh)
      then (
        // derive SALT4e3m
        let salt4e3m_m = create (size (SpecCrypto.hash_size cs)) (u8 0) in
        expand_salt4e3m prk3e2m_m th3_m salt4e3m_m;

        // extract PRK4e3m
        extract_prk4e3m salt4e3m_m ss_m prk4e3m_m;

        // Pop frame!!!
        ST.pop_frame();

        CSuccess
      )
      else (
        ST.pop_frame();

        CInvalidECPoint
      )
    )