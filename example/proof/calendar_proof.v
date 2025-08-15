From New.proof Require Import proof_prelude.
From New.proof Require Import github_com.tchajed.marshal.
From New.proof Require Import github_com.goose_lang.std.
From New.code Require Import github_com.mjschwenne.grackle.example.
From Grackle.pg Require Import github_com.mjschwenne.grackle.example.
From Grackle.example Require Import event_proof.
From New.code Require Import github_com.mjschwenne.grackle.testdata.out.go.event_gk.

Module Calendar_Proof.
Section Calendar_Proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ} {go_ctx : GoContext}.

Record C :=
    mkC {
        hash' : list u8;
        events' : list Event_Proof.C;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  ∃ (events_enc : list u8), 
  encoded = (u64_le $ length $ args.(hash')) ++ args.(hash') ++
              (u64_le $ length $ args.(events')) ++ events_enc
  /\ length args.(hash') < 2^64
  /\ encodes events_enc args.(events') Event_Proof.has_encoding
  /\ length args.(events') < 2^64.

Definition own (args__v: example.Calendar.t) (args__c: C) (dq: dfrac) : iProp Σ :=
  ∃ (l__events : list example.Event.t), 
  "Hown_hash" ∷ own_slice args__v.(example.Calendar.hash') dq args__c.(hash') ∗
  "%Hown_hash_len" ∷ ⌜ length args__c.(hash') < 2^64 ⌝ ∗
  "Hown_events_sl" ∷ own_slice args__v.(example.Calendar.events') dq l__events ∗
  "Hown_events_own" ∷ ([∗ list] x;c ∈ l__events;args__c.(events'), Event_Proof.own x c dq) ∗
  "%Hown_events_len" ∷ ⌜ length l__events < 2^64 ⌝.

Lemma wp_Encode (args__t : example.Calendar.t) (args__c : C) (pre_sl : slice.t) (prefix : list u8) (dq : dfrac):
  {{{
        is_pkg_init example ∗
        own args__t args__c dq ∗ 
        own_slice pre_sl (DfracOwn 1) prefix ∗
        own_slice_cap w8 pre_sl (DfracOwn 1)
  }}}
    @! example.MarshalCalendar #pre_sl #args__t
  {{{
        enc enc_sl, RET #enc_sl;
        ⌜ has_encoding enc args__c ⌝ ∗
        own args__t args__c dq ∗ 
        own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
        own_slice_cap w8 enc_sl (DfracOwn 1)
  }}}.

Proof.
  wp_start as "(Hown & Hsl & Hcap)". iNamed "Hown". wp_auto.

  iDestruct (own_slice_len with "Hown_hash") as "%Hown_hash_sz".
  wp_apply (wp_WriteLenPrefixedBytes with "[$Hsl $Hcap $Hown_hash]").
  iIntros (?) "(Hsl & Hcap & Hown_hash)". wp_auto.

  wp_apply (wp_WriteInt with "[$Hsl $Hcap]").
  iIntros (?) "[Hsl Hcap]". wp_auto.

  iDestruct (own_slice_len with "Hown_events_sl") as "%Hown_events_sz".
  iDestruct (big_sepL2_length with "Hown_events_own") as "%Hown_events_sz'".
  rewrite Hown_events_sz' in Hown_events_sz.
  wp_apply (wp_WriteSlice with "[$Hsl $Hcap $Hown_events_sl $Hown_events_own]").
  {
    iIntros (????) "!>".
    iIntros (?) "(Hown & Hsl & Hcap) HΦ".
    wp_apply (Event_Proof.wp_Encode with "[$Hown $Hsl $Hcap]").
    iApply "HΦ".
  }
  iIntros (events_enc events_sl') "(Hown_events & Hown_events_own & %Henc_events & Hsl & Hcap)".
  wp_auto.

  iApply "HΦ". rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding.
  split; last done.
  exists events_enc.
  split.
  {
     rewrite Hown_hash_sz.
     rewrite Hown_events_sz.
     rewrite ?w64_to_nat_id.
     congruence.
  }
  rewrite <- Hown_events_sz'.
  done. 
Qed.

Lemma wp_Decode (enc : list u8) (enc_sl : slice.t) (args__c : C) (suffix : list u8) (dq : dfrac):
  {{{
        is_pkg_init example ∗
        ⌜ has_encoding enc args__c ⌝ ∗
        own_slice enc_sl dq (enc ++ suffix)
  }}}
    @! example.UnmarshalCalendar #enc_sl
  {{{
        args__t suff_sl, RET (#args__t, #suff_sl);
        own args__t args__c (DfracOwn 1) ∗ 
        own_slice suff_sl dq suffix
  }}}.

Proof.
  wp_start as "[%Henc Hsl]". wp_auto.
  unfold has_encoding in Henc.
  destruct Henc as (events_enc & Henc & Hlen_hash & Henc_events & Hevents_sz ).
  rewrite Henc. rewrite -?app_assoc.

  wp_apply (wp_ReadLenPrefixedBytes with "[$Hsl]"); first word.
  iIntros (??) "[Hown_hash Hsl]". wp_auto.
  wp_apply (wp_BytesClone with "[$Hown_hash]").
  iIntros (?) "[Hown_hash Hown_hash_cap]". wp_auto.

  wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl". wp_auto.
  wp_apply (wp_ReadSlice  with "[$Hsl]").
  {
    iSplit; auto.
    iSplit; first word.
    iIntros (????) "!>".
    iIntros (?) "[Hsl Henc] HΦ".
    wp_apply (Event_Proof.wp_Decode with "[$Hsl $Henc]").
    iApply "HΦ".
  }
  iIntros (???) "(Hown_events_sl & Hown_events_own & Hsl)". wp_auto.
  iDestruct (big_sepL2_length with "Hown_events_own") as "%Hown_events_sz".
  rewrite <- Hown_events_sz in Hevents_sz.

  iApply "HΦ". iFrame.
  done.
Qed.

End Calendar_Proof.
End Calendar_Proof.

