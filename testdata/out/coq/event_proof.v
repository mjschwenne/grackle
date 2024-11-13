From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.event_gk.
From Grackle.test Require Import timestamp_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.timestamp_gk.

Module Event.
Section Event.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        id : u32;
        name : string;
        startTime : TimeStamp.C;
        endTime : TimeStamp.C;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  ∃ (startTime_enc endTime_enc : list u8), 
  encoded = (u32_le args.(id)) ++
              (u64_le $ length $ string_to_bytes args.(name)) ++ string_to_bytes args.(name) ++
              startTime_enc ++
              endTime_enc
  /\ TimeStamp.has_encoding startTime_enc args.(startTime)
  /\ TimeStamp.has_encoding endTime_enc args.(endTime).

Definition own (args_ptr: loc) (args: C) (dq: dfrac) : iProp Σ :=
  ∃ (startTime_l endTime_l : loc) , 
  "Hargs_id" ∷ args_ptr ↦[event_gk.S :: "Id"]{dq} #args.(id) ∗
  "Hargs_name" ∷ args_ptr ↦[event_gk.S :: "Name"]{dq} #(str args.(name)) ∗
  "Hargs_startTime" ∷ args_ptr ↦[event_gk.S :: "StartTime"]{dq} #startTime_l ∗
  "Hargs_startTime_enc" ∷ TimeStamp.own startTime_l args.(startTime) dq ∗
  "Hargs_endTime" ∷ args_ptr ↦[event_gk.S :: "EndTime"]{dq} #endTime_l ∗
  "Hargs_endTime_enc" ∷ TimeStamp.own endTime_l args.(endTime) dq.

Lemma wp_Encode (args_ptr:loc) (args:C) (pre_sl:Slice.t) (prefix:list u8) (dq: dfrac):
  {{{
        own args_ptr args dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    event_gk.Marshal #args_ptr (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own args_ptr args dq ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc)
  }}}.

Proof.
  iIntros (?) "H HΦ". iDestruct "H" as "[Hown Hsl]". iNamed "Hown".
  wp_rec. wp_pures.
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.

  wp_loadField. wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

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
  wp_apply (TimeStamp.wp_Encode with "[$Hargs_startTime_enc $Hsl]").
  iIntros (startTime_enc startTime_sl) "(%Hargs_startTime_enc & Hargs_startTime_own & Hsl)".
  wp_store.

  wp_loadField. wp_apply (wp_Assume). iIntros "%HendTime_nn".
  wp_load. wp_loadField.
  wp_apply (TimeStamp.wp_Encode with "[$Hargs_endTime_enc $Hsl]").
  iIntros (endTime_enc endTime_sl) "(%Hargs_endTime_enc & Hargs_endTime_own & Hsl)".
  wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. exists startTime_enc, endTime_enc. 
  split.
  { rewrite ?string_bytes_length.
  rewrite Hargs_name_sz.
  rewrite ?w64_to_nat_id. exact.
  }
  split.
  { exact. } { exact. }
Qed.

Lemma wp_Decode enc enc_sl (args: C) (suffix: list u8) (dq: dfrac):
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    event_gk.Unmarshal (slice_val enc_sl)
  {{{
        args_ptr suff_sl, RET (#args_ptr, suff_sl); own args_ptr args (DfracOwn 1) ∗
                                                    own_slice_small suff_sl byteT dq suffix
  }}}.

Proof.
  iIntros (?) "[%Henc Hsl] HΦ". wp_rec.
  wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hstruct". wp_pures.
  wp_apply wp_ref_to; first done.
  iIntros (?) "Hptr". wp_pures.
  iDestruct (struct_fields_split with "Hstruct") as "HH".
  iNamed "HH".

  unfold has_encoding in Henc.
  destruct Henc as ( startTime_sl & endTime_sl & Henc & Hencoding_startTime & Hencoding_endTime ).
  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (wp_ReadInt32 with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_storeField. wp_store.

  wp_apply wp_ref_of_zero; first done. iIntros (nameLen) "HnameLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (nameBytes) "HnameBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hname_sz.
  wp_apply (wp_ReadBytes with "[$]").
  { rewrite length_app in Hname_sz. word. }
  iIntros (??) "[Hname' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  wp_apply (wp_StringFromBytes with "[$Hname']"). iIntros "_".
  wp_storeField.

  wp_load. wp_apply (TimeStamp.wp_Decode startTime_sl with "[Hsl]").
  { iFrame. exact. } iIntros (??) "[HstartTime Hsl]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_apply (TimeStamp.wp_Decode endTime_sl with "[Hsl]").
  { iFrame. exact. } iIntros (??) "[HendTime Hsl]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
Qed.

End Event.
End Event.

