From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import example.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Grackle.example Require Import timestamp_proof.

Module Event.
Section Event.

Context `{!heapGS Σ}.

Record Event_ :=
  mkC {
      id : u32 ;
      startTime : Timestamp.Timestamp ;
      endTime : Timestamp.Timestamp ;
    }.

Definition has_encoding (encoded:list u8) (args:Event_) : Prop :=
  ∃ start_enc end_enc,
  encoded = (u32_le args.(id)) ++ start_enc ++ end_enc
  /\ Timestamp.has_encoding start_enc args.(startTime)
  /\ Timestamp.has_encoding end_enc args.(endTime).

Definition own args_ptr args q : iProp Σ :=
  ∃ (start_l end_l: loc),
  "Hargs_id" ∷ args_ptr ↦[Event :: "id"]{q} #args.(id) ∗
  "Hargs_start" ∷ args_ptr ↦[Event :: "start"]{q} #start_l ∗
  "Hargs_start_enc" ∷ Timestamp.own start_l args.(startTime) q ∗
  "Hargs_end" ∷ args_ptr ↦[Event :: "end"]{q} #end_l ∗
  "Hargs_end_enc" ∷ Timestamp.own end_l args.(endTime) q.

Lemma wp_Encode (args_ptr:loc) (args:Event_) (prefix:list u8) (pre_sl:Slice.t) :
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
  iIntros (?) "H HΦ". iDestruct "H" as "[Hown Hpre]". iNamed "Hown".
  wp_rec.

  unfold Event__approxSize. wp_pures.
  wp_loadField. wp_rec.
  wp_apply std_proof.wp_SumAssumeNoOverflow. iIntros "%H16".
  wp_pures. wp_loadField. wp_rec. wp_apply std_proof.wp_SumAssumeNoOverflow.
  iIntros "%H28".

  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hsl".
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.

  wp_loadField. wp_load. wp_apply (wp_WriteInt32 with "[$]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_loadField.
  wp_apply (Timestamp.wp_Encode with "[$Hargs_start_enc $Hsl]").
  iIntros (start_enc start_sl) "Hsl". iDestruct "Hsl" as (Hhe) "Hsl". wp_store.

  wp_load. wp_loadField.
  wp_apply (Timestamp.wp_Encode with "[$Hargs_end_enc $Hsl]").
  iIntros (end_enc end_sl) "Hsl". iDestruct "Hsl" as (Hhe') "Hsl". wp_store.

  wp_load. wp_apply (wp_SliceAppendSlice with "[Hpre Hsl]"); first auto.
  { iApply own_slice_to_small in "Hsl". iFrame. }
  iIntros (?) "[Hs1 Hs2]". iApply "HΦ". iFrame.
  iPureIntro.

  unfold has_encoding. exists start_enc, end_enc. split. { exact. }
  split. { exact. } { exact. }
Qed.

Lemma wp_Decode enc enc_sl (args:Event_) (suffix : list u8) (q : dfrac) :
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
  destruct Henc as [s_sl [e_sl [Henc [Hhes Hee]]]].
  rewrite Henc.

  wp_load. wp_apply (wp_ReadInt32 with "[$]"). iIntros (?) "Hs".
  wp_pures. wp_storeField. wp_store.

  wp_load. wp_apply (Timestamp.wp_Decode s_sl s' args.(startTime) (e_sl ++ suffix) q with "[Hs]").
  { rewrite app_assoc. iFrame. iPureIntro. exact. }
  iIntros (??) "[Hos Hse]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_apply (Timestamp.wp_Decode e_sl suff_sl args.(endTime) suffix q with "[Hse]").
  { iFrame. exact. } iIntros (??) "[Hoe Hss]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_pures. iApply "HΦ". iModIntro. iFrame.
Qed.

End Event.
End Event.
