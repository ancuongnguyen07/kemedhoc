module Impl.EDHOC.KeySchedule

open FStar.Mul

(*HACL related modules*)
// open Lib.RawIntTypes
open Lib.IntTypes
// open Lib.Sequence
open Lib.ByteBuffer
// lbuffer type, an immutable buffer with
// length tag, is from this module
// let lbuffer (a:Type0) (len:size_t) = lbuffer_t MUT a len
// `live` and `disjoint` are also from this module.
// Basically, HACL `Lib.Buffer` is a wrapper of `LowStar.Buffer`
// and related LowStar memory models.
open Lib.Buffer

(*LowStar related modules*)
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module Seq = Lib.Sequence

module Spec = Spec.EDHOC.KeySchedule
module SpecCrypto = Spec.EDHOC.CryptoPrimitives
module SpecParser = Spec.EDHOC.Parser

open LowStar.BufferOps

open Impl.EDHOC.CryptoPrimitives
open Impl.EDHOC.Parser
open Impl.EDHOC.Utilities
open TypeHelper.EDHOC

(*
HKDF Info, Context 2, and Context 3 related functions
are defined in `Impl.EDHOC.Parser`
*)

/// ------------------------
/// PRK
/// ------------------------

/// TH2 is Salt
/// G_XY is IKM
/// PRK2e = HKDF_Extract(TH2, G_XY)
val extract_prk2e:
  #cs:SpecCrypto.supported_cipherSuite
  -> th2_buff:hash_out_buff cs
  -> g_xy_buff:shared_secret_buf cs
  -> prk2e_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 th2_buff /\ live h0 g_xy_buff /\ live h0 prk2e_buff
    /\ B.all_disjoint [loc th2_buff; loc g_xy_buff; loc prk2e_buff]
  ))
  (ensures fun h0 _ h1 -> (
    let prk2e_abstract
      = Spec.extract_prk2e #cs (as_seq h0 th2_buff) (as_seq h0 g_xy_buff) in

    modifies1 prk2e_buff h0 h1
    /\ Seq.equal prk2e_abstract (as_seq h1 prk2e_buff)
  ))

/// SALTE3e2m is Salt
/// G_RX is Key
/// PRK3e2m = HKDF_Extract(SALT3e2m, G_RX)
/// OR PRK3e2m = PRK2e if signature-based authentication is used.
val extract_prk3e2m:
  #cs:SpecCrypto.supported_cipherSuite
  -> salt3e2m_buff:hash_out_buff cs
  -> g_rx_buff:shared_secret_buf cs
  -> prk3e2m_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 salt3e2m_buff /\ live h0 g_rx_buff /\ live h0 prk3e2m_buff
    /\ B.all_disjoint [loc salt3e2m_buff; loc g_rx_buff; loc prk3e2m_buff]
  ))
  (ensures fun h0 _ h1 -> (
    let prk3e2m_abstract
      = Spec.extract_prk3e2m #cs (as_seq h0 salt3e2m_buff) (as_seq h0 g_rx_buff) in

    modifies1 prk3e2m_buff h0 h1
    /\ Seq.equal prk3e2m_abstract (as_seq h1 prk3e2m_buff)
  ))

/// SALT4e3m is Salt
/// G_IY is Key
/// PRK4e3m = HKDF_Extract(SALT4e3m, G_IY)
/// OR PRK4e3m = PRK3e2m if signature-based authentication is used.
val extract_prk4e3m:
  #cs:SpecCrypto.supported_cipherSuite
  -> salt4e3m_buff:hash_out_buff cs
  -> g_iy_buff:shared_secret_buf cs
  -> prk4e3m_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 salt4e3m_buff /\ live h0 g_iy_buff /\ live h0 prk4e3m_buff
    /\ B.all_disjoint [loc salt4e3m_buff; loc g_iy_buff; loc prk4e3m_buff]
  ))
  (ensures fun h0 _ h1 -> (
    let prk4e3m_abstract
      = Spec.extract_prk4e3m #cs (as_seq h0 salt4e3m_buff) (as_seq h0 g_iy_buff) in

    modifies1 prk4e3m_buff h0 h1
    /\ Seq.equal prk4e3m_abstract (as_seq h1 prk4e3m_buff)
  ))

/// PRK_OUT = HKDF_Expand(PRK4e3m, 7, TH_4, hash_length)
///         = EDHOC_KDF(PRK4e3m, info, hash_length)
/// where info = {
///         label: 7,
///         context: TH_4,
///         okm_len: hash_length   
/// }
val expand_prk_out:
  #cs:SpecCrypto.supported_cipherSuite
  -> prk4e3m_buff:hash_out_buff cs
  -> th4_buff:hash_out_buff cs
  -> prk_out_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 prk4e3m_buff /\ live h0 th4_buff /\ live h0 prk_out_buff
    /\ B.all_disjoint [loc th4_buff; loc prk4e3m_buff; loc prk_out_buff]
  ))
  (ensures fun h0 _ h1 -> (
    let prk_out_abstract
      = Spec.expand_prk_out #cs (as_seq h0 prk4e3m_buff) (as_seq h0 th4_buff) in

    modifies1 prk_out_buff h0 h1
    /\ Seq.equal prk_out_abstract (as_seq h1 prk_out_buff)
  ))

/// PRK_Exporter  = HKDF_Expand(PRK_OUT, 10, empty_byte, hash_length)
///               = EDHOC_KDF(PRK_OUT, info, hash_length)
/// where info = {
///         label: 10,
///         context: empty_byte,
///         okm_len: hash_length   
/// }
val expand_prk_exporter:
  #cs:SpecCrypto.supported_cipherSuite
  -> prk_out_buff:hash_out_buff cs
  -> prk_exporter_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 -> (
    live h0 prk_out_buff /\ live h0 prk_exporter_buff
    /\ disjoint prk_out_buff prk_exporter_buff
  ))
  (ensures fun h0 _ h1 -> (
    let prk_exporter_abstract
      = Spec.expand_prk_exporter #cs (as_seq h0 prk_out_buff) in

    modifies1 prk_exporter_buff h0 h1
    /\ Seq.equal prk_exporter_abstract (as_seq h1 prk_exporter_buff)
  ))

/// ------------------------
/// Encryption key
/// ------------------------

/// KEYSTREAM2  = HKDF_Expand(PRK2e, 0, TH_2, plaintext2_length)
///             = EDHOC_KDF(PRK2e, info, plaintext2_length)
/// where info = {
///         label: 0,
///         context: TH_2,
///         okm_len: plaintext2_length   
/// }
val expand_keystream2:
  #cs:SpecCrypto.supported_cipherSuite
  -> prk2e_buff:hash_out_buff cs
  -> th2_buff:hash_out_buff cs
  -> ptx2_len:size_t{size_v ptx2_len <= SpecParser.okm_len_max_size}
  -> k2_buff:lbuffer uint8 ptx2_len
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 prk2e_buff /\ live h0 th2_buff /\ live h0 k2_buff
    /\ B.all_disjoint [loc prk2e_buff; loc th2_buff; loc k2_buff]
  )
  (ensures fun h0 _ h1 -> (
    let k2_abstract
      = Spec.expand_keystream2 #cs (as_seq h0 prk2e_buff) (as_seq h0 th2_buff) (size_v ptx2_len) in
    
    modifies1 k2_buff h0 h1
    /\ Seq.equal k2_abstract (as_seq h1 k2_buff)
  ))

/// K3  = HKDF_Expand(PRK3e2m, 3, TH_3, key_length)
///     = EDHOC_KDF(PRK3e2m, info, key_length)
/// where info = {
///         label: 3,
///         context: TH_3,
///         okm_len: key_length
/// }
val expand_k3:
  #cs:SpecCrypto.supported_cipherSuite
  -> prk3e2m_buff:hash_out_buff cs
  -> th3_buff:hash_out_buff cs
  -> k3_buff:aead_key_buff cs
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 prk3e2m_buff /\ live h0 th3_buff /\ live h0 k3_buff
    /\ B.all_disjoint [loc prk3e2m_buff; loc th3_buff; loc k3_buff]
  )
  (ensures fun h0 _ h1 -> (
    let k3_abstract
      = Spec.expand_k3 #cs (as_seq h0 prk3e2m_buff) (as_seq h0 th3_buff) in

    modifies1 k3_buff h0 h1
    /\ Seq.equal k3_abstract (as_seq h1 k3_buff)
  ))

/// ------------------------
/// Initial Vector
/// ------------------------

/// IV_3  = HKDF_Expand(PRK3e2m, 4, TH_3, iv_length)
///       = EDHOC_KDF(PRK3e2m, info, iv_length)
/// where info = {
///         label: 4,
///         context: TH_3,
///         okm_len: iv_length
/// }
val expand_iv3:
  #cs:SpecCrypto.supported_cipherSuite
  -> prk3e2m_buff:hash_out_buff cs
  -> th3_buff:hash_out_buff cs
  -> iv3_buff:aead_iv_lbuffer
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 prk3e2m_buff /\ live h0 th3_buff /\ live h0 iv3_buff
    /\ B.all_disjoint [loc prk3e2m_buff; loc th3_buff; loc iv3_buff]
  )
  (ensures fun h0 _ h1 -> (
    let iv3_abstract
      = Spec.expand_iv3 #cs (as_seq h0 prk3e2m_buff) (as_seq h0 th3_buff) in

    modifies1 iv3_buff h0 h1
    /\ Seq.equal iv3_abstract (as_seq h1 iv3_buff)
  ))

/// ------------------------
/// Salt
/// ------------------------

/// SALT3e2m  = HKDF_Expand(PRK2e, 1, TH_2, hash_length)
///           = EDHOC_KDF(PRK2e, info, hash_length)
/// where info = {
///         label: 1,
///         context: TH_2,
///         okm_len: hash_length
/// }
val expand_salt3e2m:
  #cs:SpecCrypto.supported_cipherSuite
  -> prk2e_buff:hash_out_buff cs
  -> th2_buff:hash_out_buff cs
  -> salt3e2m_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 ->
    live h0 prk2e_buff /\ live h0 th2_buff /\ live h0 salt3e2m_buff
    /\ B.all_disjoint [loc prk2e_buff; loc th2_buff; loc salt3e2m_buff]
  )
  (ensures fun h0 _ h1 -> (
    let salt3e2m_abstract
      = Spec.expand_salt3e2m #cs (as_seq h0 prk2e_buff) (as_seq h0 th2_buff) in

    modifies1 salt3e2m_buff h0 h1
    /\ Seq.equal salt3e2m_abstract (as_seq h1 salt3e2m_buff)
  ))

/// SALT4e3m  = HKDF_Expand(PRK3e2m, 5, TH_3, hash_length)
///           = EDHOC_KDF(PRK3e2m, info, hash_length)
/// where info = {
///         label: 5,
///         context: TH_3,
///         okm_len: hash_length
/// }
val expand_salt4e3m:
  #cs:SpecCrypto.supported_cipherSuite
  -> prk3e2m_buff:hash_out_buff cs
  -> th3_buff:hash_out_buff cs
  -> salt4e3m_buff:hash_out_buff cs
  -> ST.Stack unit
  (requires fun h0 -> 
    live h0 prk3e2m_buff /\ live h0 th3_buff /\ live h0 salt4e3m_buff
    /\ B.all_disjoint [loc prk3e2m_buff; loc th3_buff; loc salt4e3m_buff]
  )
  (ensures fun h0 _ h1 -> (
    let salt4e3m_abstract
      = Spec.expand_salt4e3m #cs (as_seq h0 prk3e2m_buff) (as_seq h0 th3_buff) in

    modifies1 salt4e3m_buff h0 h1
    /\ Seq.equal salt4e3m_abstract (as_seq h1 salt4e3m_buff)
  ))

/// ------------------------
/// MAC
/// ------------------------

/// MAC_2   = HKDF_Expand(PRK3e2m, 2, context_2, mac2_length)
///         = EDHOC_KDF(PRK3e2m, info, mac2_length)
/// where info = {
///         label: 2,
///         context: context_2,
///         okm_len: mac2_length
/// }
/// If signatured-based authentication then mac2_length = hash_length
/// else mac2_length = mac_length depending on cipher suite.
val expand_mac2:
  #cs:SpecCrypto.supported_cipherSuite
  -> auth_material:SpecCrypto.authentication_material
  -> prk3e2m_buff:hash_out_buff cs
  -> context2:context2_mem #cs
  -> mac2_buff:mac23_buff cs auth_material
  -> ST.Stack unit
  (requires fun h0 -> (
    is_valid_context2_mem h0 context2 /\ live h0 prk3e2m_buff /\ live h0 mac2_buff
    /\ disjoint mac2_buff prk3e2m_buff /\ context2_mem_disjoint_to context2 mac2_buff
    /\ context2_mem_disjoint_to context2 prk3e2m_buff
  ))
  (ensures fun h0 _ h1 -> (
    let context2_abstract = context2_mem_to_context2 h0 context2 in
    let mac2_abstract
      = Spec.expand_mac2 #cs auth_material (as_seq h0 prk3e2m_buff) context2_abstract in

    modifies1 mac2_buff h0 h1
    /\ Seq.equal mac2_abstract (as_seq h1 mac2_buff)
  ))

/// MAC_3 = HKDF_Expand(PRK4e3m, 6, context_3, mac3_length)
///       = EDHOC_KDF(PRK4e3m, info, mac3_length)
/// where info = {
///         label: 6,
///         context: context_3
///         okm_len: mac3_length
/// }
/// If signatured-based authentication then mac3_length = hash_length
/// else mac3_length = mac_length depending on cipher suite.
val expand_mac3:
  #cs:SpecCrypto.supported_cipherSuite
  -> auth_material:SpecCrypto.authentication_material
  -> prk4e3m_buff:hash_out_buff cs
  -> context3:context3_mem #cs
  // -> len_ctx3:size_t{len_ctx3 = context3_mem_get_length context3}
  -> mac3_buff:mac23_buff cs auth_material
  -> ST.Stack unit
  (requires fun h0 ->
    is_valid_context3_mem h0 context3 /\ live h0 prk4e3m_buff /\ live h0 mac3_buff
    /\ disjoint mac3_buff prk4e3m_buff /\ context3_mem_disjoint_to context3 mac3_buff
    /\ context3_mem_disjoint_to context3 prk4e3m_buff
  )
  (ensures fun h0 _ h1 -> (
    let context3_abstract = context3_mem_to_context3 h0 context3 in
    let mac3_abstract
      = Spec.expand_mac3 #cs auth_material (as_seq h0 prk4e3m_buff) context3_abstract in

    modifies1 mac3_buff h0 h1
    /\ Seq.equal mac3_abstract (as_seq h1 mac3_buff)
  ))