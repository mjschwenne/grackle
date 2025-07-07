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

    Definition C := main.Event.t.

    Definition has_encoding (encoded:list u8) (args:C) : Prop :=
      ∃ start_enc end_enc,
        encoded = (u32_le args.(main.Event.id')) ++
                    (u64_le $ length $ args.(main.Event.name')) ++
                    args.(main.Event.name') ++
                    start_enc ++ end_enc
        /\ length args.(main.Event.name') < 2^64
        /\ TimeStamp_Proof.has_encoding start_enc args.(main.Event.startTime')
        /\ TimeStamp_Proof.has_encoding end_enc args.(main.Event.endTime').

    Definition own (v:main.Event.t) (c:C) (dq:dfrac) : iProp Σ :=
      "%Hid" ∷ ⌜ v.(main.Event.id') = c.(main.Event.id') ⌝ ∗
      "%Hname" ∷ ⌜ v.(main.Event.name') = c.(main.Event.name') ⌝ ∗
      "HstartTime" ∷ TimeStamp_Proof.own v.(main.Event.startTime') c.(main.Event.startTime') dq ∗
      "HendTime" ∷ TimeStamp_Proof.own v.(main.Event.endTime') c.(main.Event.endTime') dq.

    Lemma wp_Encode (args__t:main.Event.t) (args__c:C) (pre_sl:slice.t) (prefix:list u8) (dq:dfrac):
      {{{
            is_pkg_init main ∗
            own args__t args__c dq ∗
            own_slice pre_sl (DfracOwn 1) prefix ∗
            own_slice_cap w8 pre_sl
      }}}
        main @ "MarshalEvent" #pre_sl #args__t
      {{{
            enc enc_sl, RET #enc_sl;
            ⌜ has_encoding enc args__c ⌝ ∗
            own args__t args__c dq ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl
      }}}.

    Proof.
      wp_start as "(Hown & Hsl & Hcap)". wp_auto.
      iNamed "Hown".

      wp_apply (wp_WriteInt32 with "[$Hsl $Hcap]").
      iIntros (?) "[Hsl Hcap]". wp_auto.

      wp_apply wp_AssumeNoStringOverflow.
      iIntros "%HnameLen". rewrite Hname in HnameLen. wp_auto.
      wp_apply wp_StringToBytes.
      iIntros (?) "Hsl'". wp_auto.

      wp_apply (wp_WriteLenPrefixedBytes with "[$Hsl $Hsl' $Hcap]").
      iIntros (?) "(Hsl & Hcap & Hname)". wp_auto.

      wp_apply (TimeStamp_Proof.wp_Encode with "[$Hsl $Hcap $HstartTime]").
      iIntros (??) "(%HstartTime & HstartTime & Hs & Hcap)". wp_auto.

      wp_apply (TimeStamp_Proof.wp_Encode with "[$Hs $Hcap $HendTime]").
      iIntros (??) "(%HendTime & HendTime & Hs & Hcap)". wp_auto.

      iApply "HΦ". rewrite -?app_assoc. iFrame.
      iSplit.
      {
      iPureIntro. unfold has_encoding. exists enc, enc0.
      rewrite Hid. rewrite Hname.
      split; first reflexivity. done.
      }
      done.
    Qed.

    Lemma wp_Decode (enc: list u8) (enc_sl: slice.t) (args__c:C) (suffix: list u8) (dq: dfrac):
      {{{
            is_pkg_init main ∗
            own_slice enc_sl dq (enc ++ suffix) ∗
            ⌜ has_encoding enc args__c ⌝
      }}}
        main @ "UnmarshalEvent" #enc_sl
      {{{
            args__t suff_sl, RET (#args__t, #suff_sl);
            own args__t args__c (DfracOwn 1) ∗
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

      wp_apply (TimeStamp_Proof.wp_Decode with "[$Hsl]"); first done.
      iIntros (??) "[HstartTime Hsl]". wp_auto.

      wp_apply (TimeStamp_Proof.wp_Decode with "[$Hsl]"); first done.
      iIntros (??) "[HendTime Hsl]". wp_auto.

      wp_apply (wp_StringFromBytes with "[$Hn]").
      iIntros "Hn". wp_auto.

      iApply "HΦ". iFrame. done.
    Qed.
  End Event_Proof.
End Event_Proof.
