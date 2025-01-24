(*****************************************)
(* This file is autogenerated by grackle *)
(*    DO NOT MANUALLY EDIT THIS FILE     *)
(*****************************************)

From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.event_gk.
From Grackle.test Require Import timestamp_proof_gk.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.timestamp_gk.

Module Event.
Section Event.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        id : u32;
        name : byte_string;
        startTime : TimeStamp.C;
        endTime : TimeStamp.C;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  ∃ (startTime_enc endTime_enc : list u8), 
  encoded = (u32_le args.(id)) ++
              (u64_le $ length $ args.(name)) ++ args.(name) ++
              startTime_enc ++
              endTime_enc
  /\ TimeStamp.has_encoding startTime_enc args.(startTime)
  /\ TimeStamp.has_encoding endTime_enc args.(endTime).

Definition own (args__v: val) (args__c: C) (dq: dfrac) : iProp Σ :=
  ∃(startTime__v endTime__v : val) , 
  "%Hown_struct" ∷ ⌜ args__v = (#args__c.(id), (#(str args__c.(name)), (startTime__v, (endTime__v, #()))))%V ⌝ ∗
  "Hown_startTime" ∷ TimeStamp.own startTime__v args__c.(startTime) dq ∗
  "Hown_endTime" ∷ TimeStamp.own endTime__v args__c.(endTime) dq.


Definition to_val' (c : C) : val :=
  (#c.(id), (#(str c.(name)), (TimeStamp.to_val' c.(startTime), (TimeStamp.to_val' c.(endTime), #())))).

Definition from_val' (v : val) : option C :=
  match v with
  | (#(LitInt32 id), (#(LitString name), (startTime, (endTime, #()))))%V =>
    match TimeStamp.from_val' startTime with
    | Some startTime =>
        match TimeStamp.from_val' endTime with
        | Some endTime =>
            Some (mkC id name startTime endTime)
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
  destruct v as [id name [startTime_hour startTime_minute startTime_second] [endTime_hour endTime_minute endTime_second]]; done.
Defined.

#[global]
Instance Event_into_val_for_type : IntoValForType C (struct.t event_gk.S).
Proof. constructor; auto 10. Defined.

Lemma own_to_val (v : val) (c : C) (dq : dfrac) :
  own v c dq -∗ ⌜ v = to_val c ⌝.
Proof.
  iIntros "Hown". iNamed "Hown".
  
  iDestruct (TimeStamp.own_to_val with "Hown_startTime") as "%Hval_startTime".
  
  iDestruct (TimeStamp.own_to_val with "Hown_endTime") as "%Hval_endTime".
  
  subst. done.
Qed.


Lemma own_val_ty :
  ∀ (v : val) (x : C) (dq : dfrac), own v x dq -∗ ⌜val_ty v (struct.t event_gk.S)⌝.
Proof.
  iIntros (???) "Hown".
  unfold own. iNamed "Hown".
  
  unfold timestamp_proof_gk.TimeStamp.own.
  iNamed "Hown_startTime".
  iNamed "Hown_endTime".
  iPureIntro.
  subst.
  repeat constructor.
Qed.

Lemma wp_Encode (args__v : val) (args__c : C) (pre_sl : Slice.t) (prefix : list u8) (dq : dfrac):
  {{{
        own args__v args__c dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    event_gk.Marshal args__v (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜ has_encoding enc args__c ⌝ ∗
        own args__v args__c dq ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc)
  }}}.

Proof.
  iIntros (?) "[Hown Hsl] HΦ".
  wp_rec. wp_pures.
  iUnfold own in "Hown". iNamed "Hown". rewrite Hown_struct.
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

  wp_load. wp_pures. wp_apply (TimeStamp.wp_Encode with "[$Hown_startTime $Hsl]").
  iIntros (startTime_enc startTime_sl) "(%Hargs_startTime_enc & Hargs_startTime_own & Hsl)".
  wp_store.

  wp_load. wp_pures. wp_apply (TimeStamp.wp_Encode with "[$Hown_endTime $Hsl]").
  iIntros (endTime_enc endTime_sl) "(%Hargs_endTime_enc & Hargs_endTime_own & Hsl)".
  wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. split.
  {
  exists startTime_enc, endTime_enc. 
  rewrite ?string_bytes_length.
  rewrite Hargs_name_sz.
  rewrite ?w64_to_nat_id. exact.
  
  } done.
Qed.

Lemma wp_Decode (enc : list u8) (enc_sl : Slice.t) (args__c : C) (suffix : list u8) (dq : dfrac):
  {{{
        ⌜ has_encoding enc args__c ⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    event_gk.Unmarshal (slice_val enc_sl)
  {{{
        args__v suff_sl, RET (args__v, suff_sl);
        own args__v args__c (DfracOwn 1) ∗
        own_slice_small suff_sl byteT dq suffix
  }}}.

Proof.
  iIntros (?) "[%Henc Hsl] HΦ". wp_rec.
  wp_apply wp_ref_to; first done.
  iIntros (l__s) "Hs". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__id) "Hid". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__name) "Hname". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__startTime) "HstartTime". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__endTime) "HendTime". wp_pures.
  
  unfold has_encoding in Henc.
  destruct Henc as ( startTime_sl & endTime_sl & Henc & Hencoding_startTime & Hencoding_endTime ).
  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (wp_ReadInt32 with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_apply wp_ref_of_zero; first done. iIntros (nameLen) "HnameLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (nameBytes) "HnameBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hname_sz.
  wp_apply (wp_ReadBytesCopy with "[$]").
  { rewrite length_app in Hname_sz. word. }
  iIntros (??) "[Hname' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  iApply own_slice_to_small in "Hname'".
  wp_apply (wp_StringFromBytes with "[$Hname']"). iIntros "_".
  wp_store.

  wp_load. wp_apply (TimeStamp.wp_Decode startTime_sl with "[$Hsl //]").
  iIntros (startTime__v ?) "[Hown_startTime Hsl]".
  iDestruct (TimeStamp.own_val_ty with "Hown_startTime") as "%Hval_startTime".
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (TimeStamp.wp_Decode endTime_sl with "[$Hsl //]").
  iIntros (endTime__v ?) "[Hown_endTime Hsl]".
  iDestruct (TimeStamp.own_val_ty with "Hown_endTime") as "%Hval_endTime".
  wp_pures. wp_store. wp_store.

  wp_load. wp_load. wp_load. wp_load. wp_load.
  wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
  iPureIntro. reflexivity.
Qed.

End Event.
End Event.

