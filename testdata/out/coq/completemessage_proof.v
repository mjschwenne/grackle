From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completemessage_gk.
From Grackle.test Require Import completeint_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completeint_gk.
From Grackle.test Require Import completeslice_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completeslice_gk.

Module completeMessage.
Section completeMessage.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        int : completeInt.C;
        slc : completeSlice.C;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  ∃ (int_enc slc_enc : list u8), 
  encoded = int_enc ++
              slc_enc
  /\ completeInt.has_encoding int_enc args.(int)
  /\ completeSlice.has_encoding slc_enc args.(slc).

Definition own (args_ptr: loc) (args: C) (dq: dfrac) : iProp Σ :=
  ∃ (int_l slc_l : loc) , 
  "Hargs_int" ∷ args_ptr ↦[completemessage_gk.S :: "Int"]{dq} #int_l ∗
  "Hargs_int_enc" ∷ completeInt.own int_l args.(int) dq ∗
  "Hargs_slc" ∷ args_ptr ↦[completemessage_gk.S :: "Slc"]{dq} #slc_l ∗
  "Hargs_slc_enc" ∷ completeSlice.own slc_l args.(slc) dq.

Lemma wp_Encode (args_ptr:loc) (args:C) (pre_sl:Slice.t) (prefix:list u8) (dq: dfrac):
  {{{
        own args_ptr args dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    completemessage_gk.Marshal #args_ptr (slice_val pre_sl)
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

  wp_loadField. wp_apply (wp_Assume). iIntros "%Hint_nn".
  wp_load. wp_loadField.
  wp_apply (completeInt.wp_Encode with "[$Hargs_int_enc $Hsl]").
  iIntros (int_enc int_sl) "(%Hargs_int_enc & Hargs_int_own & Hsl)".
  wp_store.

  wp_loadField. wp_apply (wp_Assume). iIntros "%Hslc_nn".
  wp_load. wp_loadField.
  wp_apply (completeSlice.wp_Encode with "[$Hargs_slc_enc $Hsl]").
  iIntros (slc_enc slc_sl) "(%Hargs_slc_enc & Hargs_slc_own & Hsl)".
  wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. exists int_enc, slc_enc. 
  split.
  { rewrite ?string_bytes_length.
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
    completemessage_gk.Unmarshal (slice_val enc_sl)
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
  destruct Henc as ( int_sl & slc_sl & Henc & Hencoding_int & Hencoding_slc ).
  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (completeInt.wp_Decode int_sl with "[Hsl]").
  { iFrame. exact. } iIntros (??) "[Hint Hsl]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_apply (completeSlice.wp_Decode slc_sl with "[Hsl]").
  { iFrame. exact. } iIntros (??) "[Hslc Hsl]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
Qed.

End completeMessage.
End completeMessage.

