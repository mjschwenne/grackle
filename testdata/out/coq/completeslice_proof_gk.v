(*****************************************)
(* This file is autogenerated by grackle *)
(*    DO NOT MANUALLY EDIT THIS FILE     *)
(*****************************************)

From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completeslice_gk.
From Perennial.goose_lang Require Import lib.slice.pred_slice.

Module completeSlice.
Section completeSlice.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        strg :  byte_string;
        strg2 :  byte_string;
        bytes : list u8;
        bytes2 : list u8;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le $ length $ args.(strg)) ++ args.(strg) ++
              (u64_le $ length $ args.(strg2)) ++ args.(strg2) ++
              (u64_le $ length $ args.(bytes)) ++ args.(bytes) ++
              (u64_le $ length $ args.(bytes2)) ++ args.(bytes2).

Definition own (args__v: val) (args__c: C) (dq: dfrac) : iProp Σ :=
  ∃ (bytes_sl bytes2_sl : Slice.t), 
  "%Hown_struct" ∷ ⌜ args__v = (#(str args__c.(strg)), (#(str args__c.(strg2)), (slice_val bytes_sl, (slice_val bytes2_sl, #()))))%V ⌝ ∗
  "Hown_bytes" ∷ own_slice_small bytes_sl byteT dq args__c.(bytes) ∗
  "Hown_bytes2" ∷ own_slice_small bytes2_sl byteT dq args__c.(bytes2).


Lemma own_val_ty :
  ∀ (v : val) (x : C) (dq : dfrac), own v x dq -∗ ⌜val_ty v (struct.t completeslice_gk.S)⌝.
Proof.
  iIntros (???) "Hown".
  unfold own. iNamed "Hown".
  
  iPureIntro.
  subst.
  repeat constructor.
  all: by val_ty.
Qed.

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
  wp_apply (wp_WriteBytes with "[$Hsl $Hown_bytes]").
  iIntros (?) "[Hsl Hargs_bytes_sl]". wp_store.

  iDestruct (own_slice_small_sz with "Hown_bytes2") as "%Hargs_bytes2_sz".
  wp_pures. wp_apply (wp_slice_len). wp_load.
  wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_pures. wp_load.
  wp_apply (wp_WriteBytes with "[$Hsl $Hown_bytes2]").
  iIntros (?) "[Hsl Hargs_bytes2_sl]". wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. split.
  {
  
  rewrite ?string_bytes_length.
  rewrite Hargs_strg_sz.
  rewrite Hargs_strg2_sz.
  rewrite Hargs_bytes_sz.
  rewrite Hargs_bytes2_sz.
  rewrite ?w64_to_nat_id.

  done.
  } done.
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
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__bytes2) "Hbytes2". wp_pures.
  
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

  wp_apply wp_allocN; first done; first by val_ty.
  iIntros (?) "Hbytes2Len". iApply array_singleton in "Hbytes2Len". wp_pures.
  wp_apply wp_allocN; first done; first by val_ty.
  iIntros (?) "Hbytes2Bytes". iApply array_singleton in "Hbytes2Bytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hbytes2_sz.
  wp_apply (wp_ReadBytesCopy with "[$]").
  { rewrite length_app in Hbytes2_sz. word. }
  iIntros (??) "[Hbytes2' Hsl]". iApply own_slice_to_small in "Hbytes2'".

  wp_pures. wp_store. wp_store. wp_load. wp_store.

  wp_load. wp_load. wp_load. wp_load. wp_load.
  wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
  iPureIntro. reflexivity.
Qed.

End completeSlice.
End completeSlice.

