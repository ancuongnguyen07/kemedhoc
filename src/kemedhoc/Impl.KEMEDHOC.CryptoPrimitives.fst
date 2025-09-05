module Impl.KEMEDHOC.CryptoPrimitives

// open Lib.ByteBuffer
// open Lib.Buffer
// open Lib.ByteSequence
// open Lib.IntTypes
// open LowStar.BufferOps

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

(*Specification modules*)
module Spec = Spec.KEMEDHOC.CryptoPrimitives

// open Impl.KEMEDHOC.Types

module ImplEdhocCrypto = Impl.EDHOC.CryptoPrimitives
module SpecEdhocCrypto = Spec.EDHOC.CryptoPrimitives

module ImplAEAD = EverCrypt.AEAD
module SpecAEAD = Spec.Agile.AEAD

/// Frodo Impl modules
module ImplFrodo = Hacl.Frodo.KEM
module ImplFrodoRand = Hacl.Frodo.Random

module SpecHash = Spec.Agile.Hash
module DefHash = Spec.Hash.Definitions

// open Lib.RandomBuffer.System
// open Lib.RandomSequence
module HACLRandom = Lib.RandomSequence

(*------------------ KEM*)

/// KEM key generation
let kem_keygen_frodo640 pk sk
  = (**) let h0 = ST.get() in
  ST.push_frame ();
  let kem_entr_buf = create (size Spec.kem_entr_len) (u8 0) in
  crypto_random kem_entr_buf (size Spec.kem_entr_len);
  ImplFrodoRand.randombytes_init_ kem_entr_buf;
  let _ = ImplFrodo.crypto_kem_keypair (Spec.kemAlg_to_frodo_alg Spec.Frodo640) Spec.genFrodoAlg pk sk in
  ST.pop_frame ()

/// KEM encapsulation
let kem_encaps_frodo640 pk ct ss
  = ST.push_frame ();
  let kem_entr_buf = create (size Spec.kem_entr_len) (u8 0) in
  crypto_random kem_entr_buf (size Spec.kem_entr_len);
  ImplFrodoRand.randombytes_init_ kem_entr_buf;
  let _ = ImplFrodo.crypto_kem_enc (Spec.kemAlg_to_frodo_alg Spec.Frodo640) Spec.genFrodoAlg ct ss pk in
  ST.pop_frame ()

/// KEM decapsulation
let kem_decaps_frodo640 sk ct ss
  = let _ = ImplFrodo.crypto_kem_dec (Spec.kemAlg_to_frodo_alg Spec.Frodo640) Spec.genFrodoAlg ss ct sk in
  ()