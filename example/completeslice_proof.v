From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.goose_lang Require Import lib.slice.pred_slice.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completeslice_gk.

Module completeSlice.
Section completeSlice.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        strg : byte_string;
        strg2 : byte_string;
        bytes : list u8;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le $ length $ args.(strg)) ++ args.(strg) ++
              (u64_le $ length $ args.(strg2)) ++ args.(strg2) ++
              (u64_le $ length $ args.(bytes)) ++ args.(bytes).

Definition own (args__v: val) (args__c: C) (dq: dfrac) : iProp Σ :=
  ∃(bytes_sl : Slice.t), 
  "%Hown_struct" ∷ ⌜ args__v = (#(str args__c.(strg)), (#(str args__c.(strg2)), (slice_val bytes_sl, #())))%V ⌝ ∗
  "Hown_bytes" ∷ is_pred_slice own_val bytes_sl byteT dq args__c.(bytes).

Lemma wp_Encode (args__v : val) (args__c : C) (pre_sl : Slice.t) (prefix : list u8) (dq : dfrac):
  {{{
        own args__v args__c dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    completeslice_gk.Marshal args__v (slice_val pre_sl)
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
  iUnfold is_pred_slice in "Hown_bytes".
  iDestruct "Hown_bytes" as "[%vs [Hown_bytes #HΨ_bytes]]".
  iDestruct (big_sepL2_length with "HΨ_bytes") as "%HΨ_bytes_len".
  iDestruct (big_sepL2_own_val with "HΨ_bytes") as "%HΨ_bytes_rel".
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.

  wp_apply wp_StringToBytes. iIntros (?) "Hargs_strg_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_strg_enc") as "%Hargs_strg_sz".
  iApply own_slice_to_small in "Hargs_strg_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_strg_enc]").
  iIntros (?) "[Hsl _]". wp_store.

  wp_apply wp_StringToBytes. iIntros (?) "Hargs_strg2_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_strg2_enc") as "%Hargs_strg2_sz".
  iApply own_slice_to_small in "Hargs_strg2_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_strg2_enc]").
  iIntros (?) "[Hsl _]". wp_store.

  iDestruct (own_slice_small_sz with "Hown_bytes") as "%Hargs_bytes_sz".
  wp_pures. wp_apply (wp_slice_len). wp_load.
  wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_pures. wp_load.
  wp_apply (wp_WriteBytes with "[$Hsl Hown_bytes]").
  { rewrite -> HΨ_bytes_rel.
    unfold own_slice_small.
    rewrite untype_val_list.
    iFrame. }
  iIntros (?) "[Hsl Hargs_bytes_sl]". wp_store. 


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iSplitR.
  + iPureIntro.
    unfold has_encoding.
    rewrite ?string_bytes_length.
    rewrite Hargs_strg_sz.
    rewrite Hargs_strg2_sz.
    rewrite <- HΨ_bytes_len.
    rewrite Hargs_bytes_sz.
    rewrite ?w64_to_nat_id. exact.
  + iExists bytes_sl. iSplitR; first done.
    iUnfold is_pred_slice. unfold own_slice_small. iExists (list.untype args__c.(bytes)).
    rewrite untype_val_list. iFrame. rewrite HΨ_bytes_rel. done.
Qed.

Lemma wp_Decode (enc : list u8) (enc_sl : Slice.t) (args__c : C) (suffix : list u8) (dq : dfrac):
  {{{
        ⌜ has_encoding enc args__c ⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    completeslice_gk.Unmarshal (slice_val enc_sl)
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
  iIntros (l__strg) "Hstrg". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__strg2) "Hstrg2". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__bytes) "Hbytes". wp_pures.
  
  rewrite Henc. rewrite -?app_assoc.

  wp_apply wp_ref_of_zero; first done. iIntros (strgLen) "HstrgLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (strgBytes) "HstrgBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hstrg_sz.
  wp_apply (wp_ReadBytesCopy with "[$]").
  { rewrite length_app in Hstrg_sz. word. }
  iIntros (??) "[Hstrg' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  iApply own_slice_to_small in "Hstrg'".
  wp_apply (wp_StringFromBytes with "[$Hstrg']"). iIntros "_".
  wp_store.

  wp_apply wp_ref_of_zero; first done. iIntros (strg2Len) "Hstrg2Len". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (strg2Bytes) "Hstrg2Bytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hstrg2_sz.
  wp_apply (wp_ReadBytesCopy with "[$]").
  { rewrite length_app in Hstrg2_sz. word. }
  iIntros (??) "[Hstrg2' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  iApply own_slice_to_small in "Hstrg2'".
  wp_apply (wp_StringFromBytes with "[$Hstrg2']"). iIntros "_".
  wp_store.

  wp_apply wp_allocN; first done; first by val_ty.
  iIntros (?) "HbytesLen". iApply array_singleton in "HbytesLen". wp_pures.
  wp_apply wp_allocN; first done; first by val_ty.
  iIntros (?) "HbytesBytes". iApply array_singleton in "HbytesBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hbytes_sz.
  wp_apply (wp_ReadBytesCopy with "[$]").
  { rewrite length_app in Hbytes_sz. word. }
  iIntros (??) "[Hbytes' Hsl]". iApply own_slice_to_small in "Hbytes'".

  wp_pures. wp_store. wp_store. wp_load. wp_store.

  wp_load. wp_load. wp_load. wp_load.
  wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
  iUnfold own. iExists b1. iSplitR; first done. iUnfold is_pred_slice.
  iExists (list.untype args__c.(bytes)). iSplitR "Hbytes".
  + unfold own_slice_small. rewrite untype_val_list. iFrame.
  + unfold list.untype, own_val.
    rewrite big_sepL2_fmap_l.
    rewrite <- big_sepL_sepL2_diag. done.
Qed.

End completeSlice.
End completeSlice.

