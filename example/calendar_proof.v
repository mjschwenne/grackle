From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import goose.github_com.mjschwenne.grackle.example.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Grackle.example Require Import event_proof.
From Perennial.goose_lang Require Import lib.slice.pred_slice.

Module Calendar.
  Section Calendar.

    Typeclasses Opaque app.
    Context `{!heapGS Σ}.

    Record C :=
      mkC {
          events : list Event.C;
        }.

    Definition has_encoding (encoded:list u8) (args:C) : Prop :=
      ∃ (events_enc : list u8),
        encoded = (u64_le $ length $ args.(events)) ++ events_enc /\
        encodes events_enc args.(events) Event.has_encoding.
    
    Definition own (args__v : val) (args__c : C) (dq :dfrac) : iProp Σ :=
      ∃ (events__sl : Slice.t),
        "%Hown_struct" ∷ ⌜ args__v = ((slice_val events__sl), #())%V ⌝ ∗
        "Hown_events" ∷ is_pred_slice Event.own events__sl (struct.t Event)
          dq args__c.(events).

    Lemma wp_Encode (args__v : val) (args__c : C) (prefix : list u8) (pre_sl : Slice.t) (dq: dfrac) :
      {{{
            own args__v args__c dq ∗
            own_slice pre_sl byteT (DfracOwn 1) prefix
      }}}
        MarshalCalendar args__v (slice_val pre_sl)
      {{{
            enc enc_sl, RET (slice_val enc_sl);
            ⌜ has_encoding enc args__c ⌝ ∗
            own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc) ∗
            own args__v args__c dq
      }}}.
    Proof.
      iIntros (?) "[Hown Hsl] HΦ".
      wp_rec. wp_pures.
      iUnfold own in "Hown". iNamed "Hown". rewrite Hown_struct.
      iUnfold is_pred_slice in "Hown_events".
      iDestruct "Hown_events" as "[%es [Hown_events #HΨ_events]]".
      iDestruct (big_sepL2_length with "HΨ_events") as "%HΨ_events_len".
      wp_apply (wp_ref_to); first by val_ty.
      iIntros (?) "Hptr". wp_pures.
    
      wp_apply (wp_slice_len).
      iDestruct (own_slice_small_sz with "Hown_events") as "%Hargs_events_sz".
      wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
      iIntros (?) "Hsl". wp_store. wp_pures.
      
      (* TODO: Finish once wp_WriteSlice exists *)
    Admitted.
    
    Lemma wp_Decode (enc : list u8) (enc_sl : Slice.t) (args__c : C) (suffix : list u8) (dq : dfrac) :
      (* TODO: See if this precondition can be removed. *)
      length args__c.(events) < 2^64 ->
      {{{
            ⌜ has_encoding enc args__c ⌝ ∗
            own_slice_small enc_sl byteT dq (enc ++ suffix)
      }}}
        UnmarshalCalendar (slice_val enc_sl)
      {{{
            args__v suff_sl, RET (args__v, suff_sl);
            own args__v args__c (DfracOwn 1) ∗
            own_slice_small suff_sl byteT dq suffix
      }}}.
    Proof.
      iIntros (Helen ?) "[%Henc Hsl] HΦ". wp_rec.
      wp_apply wp_ref_to; first done.
      iIntros (l__s) "Hs". wp_pures.
      
      wp_apply wp_ref_of_zero; first done.
      iIntros (l__events) "Hevents". wp_pures.

      wp_apply wp_ref_of_zero; first done.
      iIntros (l__eventsLen) "HeventsLen". wp_pures.

      destruct Henc as [events_enc [Henc Henc_events]].
      rewrite Henc. rewrite -?app_assoc.

      wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
      iIntros (?) "Hsl". wp_pures. wp_store. wp_store.

      wp_load. wp_load.

      wp_apply (wp_ReadSlice _ _ _ _ Event.has_encoding Event.own with "[Hsl]").
      {
        iIntros (???) "Hown".
        unfold Event.own.
        unfold timestamp_proof.TimeStamp.own.
        iDestruct "Hown" as "[%stv [%etv Hown]]".
        iNamed "Hown".
        iNamed "Hown_startTime".
        iNamed "Hown_endTime".
        iPureIntro.
        subst.
        repeat constructor.
      } { done. }
      { iFrame.
        iSplit; first done.
        iSplit; first word.
        iIntros (????) "!>".
        iIntros (?) "[Hsl' Henc'] HΦ".
        wp_apply (Event.wp_Decode with "[$Hsl' $Henc']").
        iApply "HΦ".
      }
      iIntros (??) "[Hpsl Hsl]".
      wp_pures. wp_store. wp_store.
      wp_load. wp_load. wp_pures.
      iModIntro. iApply "HΦ".
      iFrame. iPureIntro. done.
    Qed.
  End Calendar.
End Calendar.
    
