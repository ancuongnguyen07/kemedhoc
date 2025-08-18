module Spec.EDHOC.Base.Definitions

// let init_handshake_state
//   stat_k eph_k remote_stat_k remote_eph_k remote_cred_id
//   =
//   {
//     static = stat_k;
//     ephemeral = eph_k;
//     remote_static = remote_stat_k;
//     remote_ephemeral = remote_eph_k;
//     remote_credential_id = remote_cred_id;
//   }

let method_as_nat m
  = match m with
  | SigSig -> 1
  | SigStat -> 2
  | StatSig -> 3
  | StatStat -> 4

let label_to_method label
  = match label with
    | 1 -> SigSig
    | 2 -> SigStat
    | 3 -> StatSig
    | 4 -> StatStat

let lemma_method_as_nat_to_method_equiv m
  = ()

let lemma_label_to_method_label_equiv l
  = ()