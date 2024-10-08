From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import example.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Grackle.example Require Import timestamp_proof.

Module Event.
Section Event.

Context `{!heapGS Σ}.

Record C :=
  mkC {
      id : u32 ;
      startTime : TimeStamp.C ;
      endTime : TimeStamp.C ;
    }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  ∃ start_enc end_enc,
  encoded = (u32_le args.(id)) ++ start_enc ++ end_enc
  /\ TimeStamp.has_encoding start_enc args.(startTime)
  /\ TimeStamp.has_encoding end_enc args.(endTime).

Definition own args_ptr args q : iProp Σ :=
  ∃ (start_l end_l: loc),
  "Hargs_id" ∷ args_ptr ↦[Event :: "id"]{q} #args.(id) ∗
  "Hargs_start" ∷ args_ptr ↦[Event :: "startTime"]{q} #start_l ∗
  "Hargs_start_enc" ∷ TimeStamp.own start_l args.(startTime) q ∗
  "Hargs_end" ∷ args_ptr ↦[Event :: "endTime"]{q} #end_l ∗
  "Hargs_end_enc" ∷ TimeStamp.own end_l args.(endTime) q.

Lemma wp_Encode (args_ptr:loc) (args:C) (prefix:list u8) (pre_sl:Slice.t) :
  {{{
        own args_ptr args (DfracDiscarded) ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    MarshalEvent #args_ptr (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc)
  }}}.
Proof.
  iIntros (?) "H HΦ". iDestruct "H" as "[Hown Hsl]". iNamed "Hown".
  wp_rec. wp_pures.
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.

  wp_loadField. wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_loadField.
  wp_apply (TimeStamp.wp_Encode with "[$Hargs_start_enc $Hsl]").
  iIntros (start_enc start_sl) "Hsl".
  iDestruct "Hsl" as (Hencoding_startTime) "Hsl". wp_store.

  wp_load. wp_loadField.
  wp_apply (TimeStamp.wp_Encode with "[$Hargs_end_enc $Hsl]").
  iIntros (end_enc end_sl) "Hsl".
  iDestruct "Hsl" as (Hencoding_endTime) "Hsl". wp_store.

  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. exists start_enc, end_enc. split. { exact. }
  split. { exact. } { exact. }
Qed.

Typeclasses Opaque app.

Lemma wp_Decode enc enc_sl (args:C) (suffix : list u8) (q : dfrac) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT q (enc ++ suffix)
  }}}
    UnmarshalEvent (slice_val enc_sl)
  {{{
        args_ptr suff_sl, RET (#args_ptr, suff_sl); own args_ptr args (DfracOwn 1) ∗
                                                    own_slice_small suff_sl byteT q suffix
  }}}.
Proof.
  iIntros (?) "[%Henc Hsl] HΦ". wp_rec.
  wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hs". wp_pures.
  wp_apply wp_ref_to; first done.
  iIntros (?) "Hptr". wp_pures.
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".

  unfold has_encoding in Henc.
  destruct Henc as (startTime_sl & endTime_sl & Henc & Hencoding_startTime & Hencoding_endTime).
  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (wp_ReadInt32 with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_storeField. wp_store.

  wp_load.
  wp_apply (TimeStamp.wp_Decode startTime_sl with "[Hsl]").
  { iFrame. exact. } iIntros (??) "[HstartTime Hsl]". wp_pures. wp_storeField. wp_store.

  wp_load.
  wp_apply (TimeStamp.wp_Decode endTime_sl with "[Hsl]").
  { iFrame. exact. } iIntros (??) "[HendTime Hsl]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_pures. iApply "HΦ". iModIntro. iFrame.
Qed.

End Event.
End Event.
