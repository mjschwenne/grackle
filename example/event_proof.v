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

Definition own args_ptr args q : iProp Σ :=
  ∃ (start_l end_l: loc),
  "Hargs_id" ∷ args_ptr ↦[Event :: "id"]{q} #args.(id) ∗

  "Hargs_name" ∷ args_ptr ↦[Event :: "name"]{q} #(str args.(name)) ∗

  "Hargs_start" ∷ args_ptr ↦[Event :: "startTime"]{q} #start_l ∗
  "Hargs_start_enc" ∷ TimeStamp.own start_l args.(startTime) q ∗
  "Hargs_end" ∷ args_ptr ↦[Event :: "endTime"]{q} #end_l ∗
  "Hargs_end_enc" ∷ TimeStamp.own end_l args.(endTime) q.

Lemma wp_Encode (args_ptr:loc) (args:C) (prefix:list u8) (pre_sl:Slice.t) q :
  {{{
        own args_ptr args q ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    MarshalEvent #args_ptr (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc) ∗
        own args_ptr args q
  }}}.
Proof.
  iIntros (?) "H HΦ". iDestruct "H" as "[Hown Hsl]". iNamed "Hown".
  wp_rec. wp_pures.
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.

  wp_loadField. wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  (* iDestruct (own_slice_small_sz with "Hargs_name_enc") as "%Hargs_name_sz". *)
  wp_loadField.
  wp_apply wp_StringToBytes. iIntros (?) "Hargs_name_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_name_enc") as "%Hargs_name_sz".
  iApply own_slice_to_small in "Hargs_name_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_name_enc]").
  iIntros (?) "[Hsl _]". wp_store.

  wp_loadField. wp_apply (wp_Assume). iIntros "%HstartTime_nn".
  wp_load. wp_loadField.
  wp_apply (TimeStamp.wp_Encode with "[$Hargs_start_enc $Hsl]").
  iIntros (start_enc start_sl) "(%Hargs_start_enc & Hsl & Hargs_start_own)".
  wp_store.

  wp_loadField. wp_apply (wp_Assume). iIntros "%HendTime_nn".
  wp_load. wp_loadField.
  wp_apply (TimeStamp.wp_Encode with "[$Hargs_end_enc $Hsl]").
  iIntros (end_enc end_sl) "(%Hargs_end_enc & Hsl & Hargs_end_own)".
  wp_store.

  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. exists start_enc, end_enc. split.
  {
    rewrite ?string_bytes_length.
    rewrite Hargs_name_sz.
    rewrite w64_to_nat_id.
    exact.
  }
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
  wp_storeField.


  wp_load.
  wp_apply (TimeStamp.wp_Decode startTime_sl with "[Hsl]").
  { iFrame. exact. } iIntros (??) "[HstartTime Hsl]". wp_pures. wp_storeField. wp_store.

  wp_load.
  wp_apply (TimeStamp.wp_Decode endTime_sl with "[Hsl]").
  { iFrame. exact. } iIntros (??) "[HendTime Hsl]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
Qed.

End Event.
End Event.
