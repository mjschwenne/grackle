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

    Definition C := main.TimeStamp.t.
    
    Definition has_encoding (encoded:list u8) (args:C) : Prop :=
      encoded = (u32_le args.(main.TimeStamp.hour')) ++ (u32_le args.(main.TimeStamp.minute'))
                  ++ (u32_le args.(main.TimeStamp.second')).

    Definition own (v:main.TimeStamp.t) (c:C) (dq:dfrac) : iProp Σ :=
      ⌜ v = c ⌝.

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
            ⌜ has_encoding enc args__c ⌝ ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl ∗
            own args__t args__c dq
      }}}.

    Proof. 
        wp_start as "(Hown & Hsl & Hcap)". wp_auto.
        iDestruct "Hown" as "%Hown".

        wp_apply (wp_WriteInt32 with "[$Hsl $Hcap]").
        iIntros (?) "[Hsl Hcap]". wp_auto.

        wp_apply (wp_WriteInt32 with "[$Hsl $Hcap]").
        iIntros (?) "[Hsl Hcap]". wp_auto.

        wp_apply (wp_WriteInt32 with "[$Hsl $Hcap]").
        iIntros (?) "[Hsl Hcap]". wp_auto.

        iApply "HΦ". rewrite -?app_assoc. iFrame.
        iPureIntro. unfold has_encoding. subst.
        done.
    Qed.

    Lemma wp_Decode (enc: list u8) (enc_sl: slice.t) (args__c:C) (suffix: list u8) (dq: dfrac):
      {{{
            is_pkg_init main ∗
            own_slice enc_sl dq (enc ++ suffix) ∗
            ⌜ has_encoding enc args__c ⌝
      }}}
        main @ "UnmarshalTimeStamp" #enc_sl
      {{{
            args__t suff_sl, RET (#args__t, #suff_sl);
            own args__t args__c dq ∗
            own_slice suff_sl dq suffix
      }}}.
        
    Proof.
      wp_start as "[Hsl %Henc]". wp_auto.
      unfold has_encoding in Henc. rewrite Henc. rewrite -?app_assoc.

      wp_apply (wp_ReadInt32 with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_ReadInt32 with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_ReadInt32 with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      iApply "HΦ". iFrame.
      replace {|
       main.TimeStamp.hour' := args__c.(main.TimeStamp.hour');
       main.TimeStamp.minute' := args__c.(main.TimeStamp.minute');
       main.TimeStamp.second' := args__c.(main.TimeStamp.second')
        |} with args__c; last (destruct args__c; reflexivity).
      done.
    Qed.
  End TimeStamp_Proof.
End TimeStamp_Proof.
