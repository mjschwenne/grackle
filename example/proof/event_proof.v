From New.proof Require Import proof_prelude.
From New.code Require Import github_com.mjschwenne.grackle.example.
From Grackle.pg Require Import github_com.mjschwenne.grackle.example.
From New.proof Require Import github_com.tchajed.marshal.
From Grackle.example Require Import timestamp_proof.
From New.proof.github_com.goose_lang Require Import primitive.

Module Event_Proof.
  Section Event_Proof.

    Context `{hG: heapGS Σ, !ffi_semantics _ _}.
    Context `{!globalsGS Σ} {go_ctx : GoContext}.

    (* Timestamp defined IsPkgInit instance *)

    Definition C := example.Event.t.

    Definition has_encoding (encoded:list u8) (args:C) : Prop :=
      ∃ start_enc end_enc,
        encoded = (u32_le args.(example.Event.id')) ++
                    (u64_le $ length $ args.(example.Event.name')) ++
                    args.(example.Event.name') ++
                    start_enc ++ end_enc
        /\ length args.(example.Event.name') < 2^64
        /\ TimeStamp_Proof.has_encoding start_enc args.(example.Event.startTime')
        /\ TimeStamp_Proof.has_encoding end_enc args.(example.Event.endTime').

    Definition own (v:example.Event.t) (c:C) (dq:dfrac) : iProp Σ :=
      "%Hid" ∷ ⌜ v.(example.Event.id') = c.(example.Event.id') ⌝ ∗
      "%Hname" ∷ ⌜ v.(example.Event.name') = c.(example.Event.name') ⌝ ∗
      "HstartTime" ∷ TimeStamp_Proof.own v.(example.Event.startTime') c.(example.Event.startTime') dq ∗
      "HendTime" ∷ TimeStamp_Proof.own v.(example.Event.endTime') c.(example.Event.endTime') dq.

    Lemma wp_Encode (args__t:example.Event.t) (args__c:C) (pre_sl:slice.t) (prefix:list u8) (dq:dfrac):
      {{{
            is_pkg_init example ∗
            own args__t args__c dq ∗
            own_slice pre_sl (DfracOwn 1) prefix ∗
            own_slice_cap w8 pre_sl (DfracOwn 1)
      }}}
        @! example.MarshalEvent #pre_sl #args__t
      {{{
            enc enc_sl, RET #enc_sl;
            ⌜ has_encoding enc args__c ⌝ ∗
            own args__t args__c dq ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl (DfracOwn 1)
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
            is_pkg_init example ∗
            own_slice enc_sl dq (enc ++ suffix) ∗
            ⌜ has_encoding enc args__c ⌝
      }}}
        @! example.UnmarshalEvent #enc_sl
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
