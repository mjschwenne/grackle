From New.proof Require Import proof_prelude.
From Grackle.new_ex Require Import goose.github_com.mjschwenne.grackle.new_example.
From Grackle.new_ex Require Import pg.github_com.mjschwenne.grackle.new_example.
From New.proof Require Import github_com.tchajed.marshal.
From Grackle.new_ex Require Import timestamp_proof.

Module Event_Proof.
  Section Event_Proof.

    Context `{hG: heapGS Σ, !ffi_semantics _ _}.
    Context `{!goGlobalsGS Σ}.

    #[global]
      Program Instance : IsPkgInit main :=
        ltac2:(build_pkg_init ()).

    Definition has_encoding (encoded:list u8) (args:main.Event.t) : Prop :=
      ∃ start_enc end_enc,
        encoded = (u32_le args.(main.Event.id')) ++
                    (u64_le $ length $ args.(main.Event.name')) ++
                    args.(main.Event.name') ++
                    start_enc ++ end_enc
        /\ TimeStamp_Proof.has_encoding start_enc args.(main.Event.startTime')
        /\ TimeStamp_Proof.has_encoding end_enc args.(main.Event.endTime').

    Lemma wp_Encode (args__c:main.Event.t) (pre_sl:slice.t) (prefix:list u8) (dq:dfrac):
      {{{
            is_pkg_init main ∗
            own_slice pre_sl (DfracOwn 1) prefix ∗
            own_slice_cap w8 pre_sl
      }}}
        main @ "MarshalEvent" #pre_sl #args__c
      {{{
            enc enc_sl, RET #enc_sl;
            ⌜ has_encoding enc args__c ⌝ ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl
      }}}.

    Proof.
      wp_start as "[Hsl Hcap]". wp_auto.

      wp_apply (wp_WriteInt32 with "[$Hsl $Hcap]").
      iIntros (?) "[Hsl Hcap]". wp_auto.

    Admitted.
  End Event_Proof.
End Event_Proof.
