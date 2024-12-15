From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import goose.github_com.mjschwenne.grackle.example.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Grackle.example Require Import timestamp_proof.

Module Event.
Section Event.

Context `{!heapGS Σ}.

Record C :=
  mkC {
      id : u32 ;
      name : string ;
      startTime : TimeStamp.C ;
      endTime : TimeStamp.C ;
    }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  ∃ start_enc end_enc,
    encoded = (u32_le args.(id)) ++
              (u64_le $ length $ string_to_bytes args.(name)) ++ string_to_bytes args.(name) ++
              start_enc ++ end_enc
    /\ TimeStamp.has_encoding start_enc args.(startTime)
    /\ TimeStamp.has_encoding end_enc args.(endTime).

Definition own (args__v : val) (args__c : C) (dq : dfrac) : iProp Σ :=
  ∃ (startTime__v endTime__v: val),
    "%Hown_struct" ∷ ⌜ args__v = (#args__c.(id), (#(str args__c.(name)), (startTime__v, (endTime__v, #()))))%V ⌝ ∗
    "Hown_startTime" ∷ TimeStamp.own startTime__v args__c.(startTime) dq ∗
    "Hown_endTime" ∷ TimeStamp.own endTime__v args__c.(endTime) dq.

Definition to_val' (c : C) : val :=
  (#c.(id), (#(str c.(name)), (TimeStamp.to_val' c.(startTime), (TimeStamp.to_val' c.(endTime), #())))).

Definition from_val' (v : val) : option C :=
  match v with
  | (#(LitInt32 i), (#(LitString n), (s, (e, #()))))%V =>
      match TimeStamp.from_val' s with
      | Some s' =>
          match TimeStamp.from_val' e with
          | Some e' => Some (mkC i n s' e')
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

#[global]
Instance Event_into_val : IntoVal C.
Proof.
  refine {|
      to_val := to_val';
      from_val := from_val';
      IntoVal_def := (mkC (W32 0) "" (IntoVal_def TimeStamp.C) (IntoVal_def TimeStamp.C))
    |}.
  intros v.
  destruct v as [i n [sh sm ss] [eh em es]]; done.
Defined.

#[global]
Instance Event_into_val_for_type : IntoValForType C (struct.t Event).
Proof. constructor; auto 10. Defined.

Lemma own_to_val (v : val) (c : C) (dq : dfrac) :
  own v c dq -∗ own v c dq ∗ ⌜ v = to_val c ⌝.
Proof.
  iIntros "Hown".
  iNamed "Hown".
  iApply (TimeStamp.own_to_val) in "Hown_startTime".
  iDestruct "Hown_startTime" as "[Hown_startTime %Hval_startTime]".
  iApply (TimeStamp.own_to_val) in "Hown_endTime".
  iDestruct "Hown_endTime" as "[Hown_endTime %Hval_endTime]".
  iUnfold own.
  iSplitL.
  + iExists startTime__v, endTime__v. iFrame. iPureIntro. done.
  + rewrite Hown_struct.
    rewrite Hval_startTime.
    rewrite Hval_endTime.
    iPureIntro. reflexivity.
Qed.

Lemma wp_Encode (args__v : val) (args__c : C) (prefix : list u8) (pre_sl : Slice.t) (dq : dfrac) :
  {{{
        own args__v args__c dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    MarshalEvent args__v (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜ has_encoding enc args__c ⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc) ∗
        own args__v args__c dq
  }}}.
Proof.
  iIntros (?) "[Hown Hsl] HΦ". iNamed "Hown". rewrite Hown_struct.
  wp_rec. wp_pures.
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.

  wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_apply wp_StringToBytes. iIntros (?) "Hargs_name_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_name_enc") as "%Hargs_name_sz".
  iApply own_slice_to_small in "Hargs_name_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_name_enc]").
  iIntros (?) "[Hsl _]". wp_store.

  wp_load. wp_apply (TimeStamp.wp_Encode with "[$Hown_startTime $Hsl]").
  iIntros (start_enc start_sl) "(%Hargs_start_enc & Hsl & Hargs_start_own)".
  wp_store.

  wp_load. wp_apply (TimeStamp.wp_Encode with "[$Hown_endTime $Hsl]").
  iIntros (end_enc end_sl) "(%Hargs_end_enc & Hsl & Hargs_end_own)".
  wp_store.

  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. split.
  {
    exists start_enc, end_enc.
    rewrite ?string_bytes_length.
    rewrite Hargs_name_sz.
    rewrite w64_to_nat_id.
    exact.
  }
  done.
Qed.

Typeclasses Opaque app.

Lemma wp_Decode enc enc_sl (args__c : C) (suffix : list u8) (dq : dfrac) :
  {{{
        ⌜ has_encoding enc args__c ⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    UnmarshalEvent (slice_val enc_sl)
  {{{
        args__v suff_sl, RET (args__v, suff_sl); own args__v args__c (DfracOwn 1) ∗
                                                    own_slice_small suff_sl byteT dq suffix
  }}}.
Proof.
  iIntros (?) "[%Henc Hsl] HΦ". wp_rec.
  wp_apply wp_ref_to; first done.
  iIntros (?) "Hptr". wp_pures.

  wp_apply wp_ref_of_zero; first done.
  iIntros (l__id) "Hid". wp_pures.

  wp_apply wp_ref_of_zero; first done.
  iIntros (l__name) "Hname". wp_pures.

  wp_apply wp_ref_of_zero; first done.
  iIntros (l__startTime) "HstartTime". wp_pures.

  wp_apply wp_ref_of_zero; first done.
  iIntros (l__endTime) "HendTime". wp_pures.

  unfold has_encoding in Henc.
  destruct Henc as (startTime_sl & endTime_sl & Henc & Hencoding_startTime & Hencoding_endTime).
  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (wp_ReadInt32 with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_apply wp_ref_of_zero; first done. iIntros (nameLen) "HnameLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (nameBytes) "HnameBytes". wp_pures.

  wp_load. wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl". wp_pures. wp_store. wp_store.
  wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hsz.
  wp_apply (wp_ReadBytesCopy with "[$]").
  { rewrite length_app in Hsz. word. }
  iIntros (??) "[Hname' Hsl]". iApply own_slice_to_small in "Hname'".

  wp_pures. wp_store. wp_store. wp_load.
  wp_apply (wp_StringFromBytes with "[$Hname']"). iIntros "_".
  wp_store.

  wp_load.
  wp_apply (TimeStamp.wp_Decode startTime_sl with "[$Hsl //]").
  iIntros (startTime__v ?) "[Hown_startTime Hsl]".
  iApply (TimeStamp.own_to_val) in "Hown_startTime".
  iDestruct "Hown_startTime" as "[Hown_startTime %Hval_startTime]".
  rewrite Hval_startTime.
  wp_pures. wp_store. wp_store.

  wp_load.
  wp_apply (TimeStamp.wp_Decode endTime_sl with "[Hsl]").
  { iFrame. exact. } iIntros (endTime__v ?) "[Hown_endTime Hsl]".
  iApply (TimeStamp.own_to_val) in "Hown_endTime".
  iDestruct "Hown_endTime" as "[Hown_endTime %Hval_endTime]".
  rewrite Hval_endTime.
  wp_pures. wp_store. wp_store.

  wp_load. wp_load. wp_load. wp_load. wp_load.
  wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
  iPureIntro. reflexivity.
Qed.

End Event.
End Event.
