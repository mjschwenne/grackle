From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.complete_gk.
From Grackle.test Require Import completeint_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completeint_gk.
From Grackle.test Require Import completeslice_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completeslice_gk.

Module complete.
Section complete.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        int : completeInt.C;
        slc : completeSlice.C;
        success : bool;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  ∃ (int_enc slc_enc : list u8), 
  encoded = int_enc ++
              slc_enc ++
              [if args.(success) then W8 1 else W8 0]
  /\ completeInt.has_encoding int_enc args.(int)
  /\ completeSlice.has_encoding slc_enc args.(slc).

Definition own (args__v: val) (args__c: C) (dq: dfrac) : iProp Σ :=
  ∃ (int__v slc__v:val),
  "%Hown_struct" ∷ ⌜ args__v = (int__v, (slc__v, (#args__c.(success), #())))%V ⌝ ∗
  "Hown_int" ∷ completeInt.own int__v args__c.(int) dq ∗
  "Hown_slc" ∷ completeSlice.own slc__v args__c.(slc) dq.

Lemma wp_Encode (args__v : val) (args__c : C) (pre_sl : Slice.t) (prefix : list u8) (dq : dfrac):
  {{{
        own args__v args__c dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    complete_gk.Marshal args__v (slice_val pre_sl)
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

  wp_load. wp_pures. wp_apply (completeInt.wp_Encode with "[$Hown_int $Hsl]").
  iIntros (int_enc int_sl) "(%Hargs_int_enc & Hargs_int_own & Hsl)".
  wp_store.

  wp_load. wp_pures. wp_apply (completeSlice.wp_Encode with "[$Hown_slc $Hsl]").
  iIntros (slc_enc slc_sl) "(%Hargs_slc_enc & Hargs_slc_own & Hsl)".
  wp_store.

  wp_load. wp_apply (wp_WriteBool with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. split.
  {
  exists int_enc, slc_enc. 
  rewrite ?string_bytes_length.
  rewrite ?w64_to_nat_id. exact.
  
  } done.
Qed.

Lemma wp_Decode (enc : list u8) (enc_sl : Slice.t) (args__c : C) (suffix : list u8) (dq : dfrac):
  {{{
        ⌜ has_encoding enc args__c ⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    complete_gk.Unmarshal (slice_val enc_sl)
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
  iIntros (l__int) "Hint". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__slc) "Hslc". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__success) "Hsuccess". wp_pures.
  
  unfold has_encoding in Henc.
  destruct Henc as ( int_sl & slc_sl & Henc & Hencoding_int & Hencoding_slc ).
  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (completeInt.wp_Decode int_sl with "[$Hsl //]").
  iIntros (int__v ?) "[Hown_int Hsl]".
  iApply (completeInt.own_to_val) in "Hown_int".
  iDestruct "Hown_int" as "[Hown_int %Hval_int]".
  rewrite Hval_int.
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (completeSlice.wp_Decode slc_sl with "[$Hsl //]").
  iIntros (slc__v ?) "[Hown_slc Hsl]".
  iUnfold completeSlice.own in "Hown_slc".
  iDestruct "Hown_slc" as "[%slc_sl_sl [%Hval_slc Hown_slc]]".
  rewrite Hval_slc.
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (wp_ReadBool with "[Hsl]").
  { simpl. iFrame. }
  iIntros (success_b ?) "[%Hsuccess Hsl]".
  assert (success_b = args__c.(success)) as Hargs_success.
  { destruct args__c.(success); rewrite Hsuccess; reflexivity. }
  rewrite Hargs_success.
  wp_pures. wp_store. wp_store.

  wp_load. wp_load. wp_load. wp_load.
  wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
  iExists slc__v. iSplitL; iPureIntro; rewrite Hval_slc; reflexivity.
Qed.

End complete.
End complete.

