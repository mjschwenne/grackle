From New.proof Require Import proof_prelude.
From Grackle.new_ex Require Import goose.github_com.mjschwenne.grackle.new_example.
From Grackle.new_ex Require Import pg.github_com.mjschwenne.grackle.new_example.
From New.proof Require Import github_com.tchajed.marshal.
From Grackle.new_ex Require Import timestamp_proof.
From New.proof.github_com.goose_lang Require Import primitive.

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
        /\ length args.(main.Event.name') < 2^64
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

      wp_apply wp_AssumeNoStringOverflow.
      iIntros "%HnameLen". wp_auto.
      wp_apply wp_StringToBytes.
      iIntros (?) "Hsl'". wp_auto.

      wp_apply (wp_WriteLenPrefixedBytes with "[$Hsl $Hsl' $Hcap]").
      iIntros (?) "(Hs & Hcap & Hsl)". wp_auto.

      wp_apply (TimeStamp_Proof.wp_Encode with "[$Hs $Hcap]"); first trivial.
      iIntros (??) "(%HstartTime & Hs & Hcap)". wp_auto.

      wp_apply (TimeStamp_Proof.wp_Encode with "[$Hs $Hcap]"); first trivial.
      iIntros (??) "(%HendTime & Hs & Hcap)". wp_auto.

      iApply "HΦ". rewrite -?app_assoc. iFrame.
      iPureIntro. unfold has_encoding. exists enc, enc0.
      split; first reflexivity. done.
    Qed.

    Lemma wp_Decode (enc: list u8) (enc_sl: slice.t) (args__c:main.Event.t) (suffix: list u8) (dq: dfrac):
      {{{
            is_pkg_init main ∗
            own_slice enc_sl dq (enc ++ suffix) ∗
            ⌜ has_encoding enc args__c ⌝
      }}}
        main @ "UnmarshalEvent" #enc_sl
      {{{
            suff_sl, RET (#args__c, #suff_sl);
            own_slice suff_sl dq suffix
      }}}.

    Proof.
      wp_start as "[Hsl %Henc]". wp_auto.
      unfold has_encoding in Henc.
      destruct Henc as (start_enc & end_enc & Henc & Hnlen & Henc_st & Henc_et).
      rewrite Henc. rewrite -?app_assoc.

      wp_apply (wp_ReadInt32 with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_ReadLenPrefixedBytes with "[$Hsl]"); first word.
      iIntros (??) "[Hn Hsl]". wp_auto.

      wp_apply (TimeStamp_Proof.wp_Decode with "[$Hsl]"); first trivial.
      iIntros (?) "Hsl". wp_auto.

      wp_apply (TimeStamp_Proof.wp_Decode with "[$Hsl]"); first trivial.
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_StringFromBytes with "[$Hn]").
      iIntros "Hn". wp_auto.

      replace {|
          main.Event.id' := args__c.(main.Event.id');
          main.Event.name' := args__c.(main.Event.name');
          main.Event.startTime' := args__c.(main.Event.startTime');
          main.Event.endTime' := args__c.(main.Event.endTime')
        |} with args__c; last (destruct args__c; reflexivity).
      iApply "HΦ". iFrame.
    Qed.
  End Event_Proof.
End Event_Proof.
