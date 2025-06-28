From New.proof Require Import proof_prelude.
From Grackle.new_ex Require Import goose.github_com.mjschwenne.grackle.new_example.
From Grackle.new_ex Require Import pg.github_com.mjschwenne.grackle.new_example.
From New.proof Require Import github_com.tchajed.marshal.

Module TimeStamp_Proof.
  Section TimeStamp_Proof.

    Context `{hG: heapGS Σ, !ffi_semantics _ _}.
    Context `{!goGlobalsGS Σ}.

    #[global]
    Program Instance : IsPkgInit main :=
        ltac2:(build_pkg_init ()).

    Record C :=
      mkC {
          hour: u32;
          minute: u32;
          second: u32;
      }.

    (* Definition has_encoding (encoded:list u8) (args:main.TimeStamp.t) : Prop := *)
    (*   encoded = (u32_le args.(main.TimeStamp.hour')) ++ (u32_le args.(main.TimeStamp.minute')) *)
    (*               ++ (u32_le args.(main.TimeStamp.second')). *)

    Definition has_encoding' (encoded:list u8) (args:C) : Prop :=
      encoded = (u32_le args.(hour)) ++ (u32_le args.(minute))
                  ++ (u32_le args.(second)).

    Definition own (v:main.TimeStamp.t) (c:C) (dq:dfrac) : iProp Σ :=
      ⌜ v.(main.TimeStamp.hour') = c.(hour) ⌝ ∗
      ⌜ v.(main.TimeStamp.minute') = c.(minute) ⌝ ∗
      ⌜ v.(main.TimeStamp.second') = c.(second) ⌝. 

    Lemma wp_Encode (args__t : main.TimeStamp.t) (args__c:C) (pre_sl : slice.t) (prefix : list u8) (dq : dfrac):
      {{{
            is_pkg_init main ∗
            own args__t args__c dq ∗
            own_slice pre_sl (DfracOwn 1) prefix ∗
            own_slice_cap w8 pre_sl
      }}}
        main @ "MarshalTimeStamp" #pre_sl #args__t
      {{{
            enc enc_sl, RET #enc_sl;
            ⌜ has_encoding' enc args__c ⌝ ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl ∗
            own args__t args__c dq
      }}}.

    Proof. 
        wp_start as "(Hown & Hsl & Hcap)". wp_auto.
        iDestruct "Hown" as "(%Hhour & %Hminute & %Hsecond)".

        wp_apply (wp_WriteInt32 with "[$Hsl $Hcap]").
        iIntros (?) "[Hsl Hcap]". wp_auto.

        wp_apply (wp_WriteInt32 with "[$Hsl $Hcap]").
        iIntros (?) "[Hsl Hcap]". wp_auto.

        wp_apply (wp_WriteInt32 with "[$Hsl $Hcap]").
        iIntros (?) "[Hsl Hcap]". wp_auto.

        iApply "HΦ". rewrite -?app_assoc. iFrame.
        iPureIntro. unfold has_encoding'.
        rewrite Hhour. rewrite Hminute. rewrite Hsecond.
        done.
    Qed.

    Lemma wp_Decode (enc: list u8) (enc_sl: slice.t) (args__c:C) (suffix: list u8) (dq: dfrac):
      {{{
            is_pkg_init main ∗
            own_slice enc_sl dq (enc ++ suffix) ∗
            ⌜ has_encoding' enc args__c ⌝
      }}}
        main @ "UnmarshalTimeStamp" #enc_sl
      {{{
            args__t suff_sl, RET (#args__t, #suff_sl);
            own args__t args__c dq ∗
            own_slice suff_sl dq suffix
      }}}.
        
    Proof.
      wp_start as "[Hsl %Henc]". wp_auto.
      unfold has_encoding' in Henc. rewrite Henc. rewrite -?app_assoc.

      wp_apply (wp_ReadInt32 with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_ReadInt32 with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_ReadInt32 with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      (* replace {| *)
      (*  main.TimeStamp.hour' := args__c.(hour); *)
      (*  main.TimeStamp.minute' := args__c.(minute); *)
      (*  main.TimeStamp.second' := args__c.(second) *)
      (*   |} with args__t; last (destruct args__t; reflexivity). *)
      iApply "HΦ". iFrame. done.
    Qed.
  End TimeStamp_Proof.
End TimeStamp_Proof.
