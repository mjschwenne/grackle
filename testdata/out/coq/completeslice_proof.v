From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completeslice_gk.

Module completeSlice.
Section completeSlice.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        strg : string;
        byte : list u8;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le $ length $ string_to_bytes args.(strg)) ++ string_to_bytes args.(strg) ++
              (u64_le $ length $ args.(byte)) ++ args.(byte).

Definition own (args_ptr: loc) (args: C) (dq: dfrac) : iProp Σ :=
  ∃ (byte_sl : Slice.t), 
  "Hargs_strg" ∷ args_ptr ↦[completeslice_gk.S :: "Strg"]{dq} #(str args.(strg)) ∗
  "Hargs_byte" ∷ args_ptr ↦[completeslice_gk.S :: "Byte"]{dq} (slice_val byte_sl) ∗
  "Hargs_byte_sl" ∷ own_slice_small byte_sl byteT dq args.(byte)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) (pre_sl:Slice.t) (prefix:list u8) (dq: dfrac):
  {{{
        own args_ptr args dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    completeslice_gk.Marshal #args_ptr (slice_val pre_sl)
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

  wp_loadField.
  wp_apply wp_StringToBytes. iIntros (?) "Hargs_strg_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_strg_enc") as "%Hargs_strg_sz".
  iApply own_slice_to_small in "Hargs_strg_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_strg_enc]").
  iIntros (?) "[Hsl _]". wp_store.

  iDestruct (own_slice_small_sz with "Hargs_byte_sl") as "%Hargs_byte_sz".
  wp_loadField. wp_apply wp_slice_len. wp_load.
  wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.

  wp_loadField. wp_load.
  wp_apply (wp_WriteBytes with "[$Hsl $Hargs_byte_sl]").
  iIntros (?) "[Hsl Hargs_byte_sl]". wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. 
  rewrite ?string_bytes_length.
  rewrite Hargs_strg_sz.
  rewrite Hargs_byte_sz.
  rewrite ?w64_to_nat_id. exact.

Qed.

Lemma wp_Decode enc enc_sl (args: C) (suffix: list u8) (dq: dfrac):
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    completeslice_gk.Unmarshal (slice_val enc_sl)
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
  wp_storeField.

  wp_apply wp_allocN; first done; first by val_ty.
  iIntros (?) "HbyteLen". iApply array_singleton in "HbyteLen". wp_pures.
  wp_apply wp_allocN; first done; first by val_ty.
  iIntros (?) "Hbyte". iApply array_singleton in "Hbyte". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hbyte_sz.
  wp_apply (wp_ReadBytesCopy with "[$]").
  { rewrite length_app in Hbyte_sz. word. }
  iIntros (??) "[Hbyte' Hsl]". iApply own_slice_to_small in "Hbyte'".

  wp_pures. wp_store. wp_store. wp_load. wp_storeField.

  wp_load. wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
Qed.

End completeSlice.
End completeSlice.
