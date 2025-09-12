module Impl.KEMEDHOC.Core

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module Spec = Spec.KEMEDHOC.Core
friend Spec.KEMEDHOC.Core
module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives

(*Specification modules*)
module SpecCrypto = Spec.KEMEDHOC.CryptoPrimitives
module SpecSerdEdhoc = Spec.EDHOC.Serialization
module SpecParser = Spec.KEMEDHOC.Parser

module TypeEdhoc = TypeHelper.EDHOC

#push-options "--z3rlimit 10"
let init_handshake_state #kcs hs
  = lbufferOpt_set_None hs.k_xy;
  lbufferOpt_set_None hs.k_auth_I;
  lbufferOpt_set_None hs.th2;
  lbufferOpt_set_None hs.th3;
  lbufferOpt_set_None hs.th4;
  lbufferOpt_set_None hs.prk2e;
  lbufferOpt_set_None hs.prk3e2m;
  lbufferOpt_set_None hs.prk4e3m;
  lbufferOpt_set_None hs.prk_out;
  lbufferOpt_set_None hs.prk_exporter;
  lbufferOpt_set_None hs.remote_id_cred

#pop-options