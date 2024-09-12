From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import example.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Grackle.example Require Import marshal_proof.

Module encodeEvent.
Section encodeEvent.

Context `{!heapGS Σ}.

Record EventStruct :=
  mkC {
      id : u32 ;
      startTime : encodeTimestamp.Timestamp ;
      endTime : encodeTimestamp.Timestamp ;
    }.

Definition has_encoding (encoded:list u8) (args:EventStruct) : Prop :=
  ∃ start_enc end_enc,
  encoded = (u32_le args.(id)) ++ start_enc ++ end_enc
  /\ encodeTimestamp.has_encoding start_enc args.(startTime)
  /\ encodeTimestamp.has_encoding end_enc args.(endTime).

Definition own args_ptr args q : iProp Σ :=
  ∃ (start_l end_l: loc),
  "Hargs_id" ∷ args_ptr ↦[Event :: "id"]{q} #args.(id) ∗
  "Hargs_start" ∷ args_ptr ↦[Event :: "start"]{q} #start_l ∗
  "Hargs_start_enc" ∷ encodeTimestamp.own start_l args.(startTime) q ∗
  "Hargs_end" ∷ args_ptr ↦[Event :: "end"]{q} #end_l ∗
  "Hargs_end_enc" ∷ encodeTimestamp.own end_l args.(endTime) q.

Lemma wp_Encode (args_ptr:loc) (args:EventStruct) (prefix:list u8) (pre_sl:Slice.t) :
  {{{
        "Hown" ∷ own args_ptr args (DfracDiscarded) ∗
        "Hpre" ∷ own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    MarshalEvent #args_ptr (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc)
  }}}.
Proof.
  iIntros (?) "H HΦ". iNamed "H". iNamed "Hown". wp_rec.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hsl".
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr".
  wp_pures.

  wp_loadField. wp_load. wp_apply (wp_WriteInt32 with "[$]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_loadField.
  wp_apply (encodeTimestamp.wp_Encode with "[$Hargs_start_enc $Hsl]").
  iIntros (??) "Hsl". iDestruct "Hsl" as (Hhe) "Hsl". wp_store.

  wp_load. wp_loadField.
  wp_apply (encodeTimestamp.wp_Encode with "[$Hargs_end_enc $Hsl]").
  iIntros (??) "Hsl". iDestruct "Hsl" as (Hhe') "Hsl". wp_store.

  wp_load. wp_apply (wp_SliceAppendSlice with "[Hpre Hsl]"); first auto.
  { iApply own_slice_to_small in "Hsl". iFrame. }
  iIntros (?) "[Hs1 Hs2]". iApply "HΦ". iFrame.
  iPureIntro.
  unfold has_encoding. exists enc, enc0. split; first done.
  split.
  - exact.
  - exact.
Qed.

Lemma wp_Decode enc enc_sl (args:EventStruct) (suffix : list u8) (q : dfrac) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT (DfracOwn 1) (enc ++ suffix)
  }}}
    UnmarshalEvent (slice_val enc_sl)
  {{{
        args_ptr suff_sl, RET (#args_ptr, suff_sl); own args_ptr args (DfracOwn 1) ∗
                                                    own_slice_small suff_sl byteT (DfracOwn 1) suffix
  }}}.
Proof.
  iIntros (?) "[%Henc Hsl] HΦ". wp_rec.
  wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hs". wp_pures.
  wp_apply wp_ref_to; first done.
  iIntros (?) "Hptr". wp_pures.
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".

  unfold has_encoding in Henc. destruct Henc as [s_sl Hend]. destruct Hend as [e_sl Hconj].
  destruct Hconj as [Henc Hhe2] . destruct Hhe2 as [Hhes Hhee]. rewrite Henc.

  wp_load. wp_apply (wp_ReadInt32 with "[$]"). iIntros (?) "Hs".
  wp_pures. wp_storeField. wp_store.

  wp_load. wp_apply (encodeTimestamp.wp_Decode s_sl s' args.(startTime) (e_sl ++ suffix) (DfracOwn 1) with "[Hs]").
  { rewrite app_assoc. iFrame. iPureIntro. exact. }
  iIntros (??) "[Hos Hse]".
  wp_pures. wp_storeField. wp_store.

  wp_load. wp_apply (encodeTimestamp.wp_Decode e_sl suff_sl args.(endTime) suffix (DfracOwn 1) with "[Hse]").
  { iFrame. exact. }
  iIntros (??) "[Hoe Hss]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_pures. iApply "HΦ". iModIntro. iFrame.
Qed.

End encodeEvent.
End encodeEvent.
