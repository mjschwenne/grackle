(*****************************************)
(* This file is autogenerated by grackle *)
(*    DO NOT MANUALLY EDIT THIS FILE     *)
(*****************************************)

From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completeint_gk.
From Perennial.goose_lang Require Import lib.slice.pred_slice.

Module completeInt.
Section completeInt.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        one :  u32;
        two :  u32;
        three :  u32;
        four :  u64;
        five :  u64;
        six :  u64;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u32_le args.(one)) ++
              (u32_le args.(two)) ++
              (u32_le args.(three)) ++
              (u64_le args.(four)) ++
              (u64_le args.(five)) ++
              (u64_le args.(six)).

Definition own (args__v: val) (args__c: C) (dq: dfrac) : iProp Σ :=
  "%Hown_struct" ∷ ⌜ args__v = (#args__c.(one), (#args__c.(two), (#args__c.(three), (#args__c.(four), (#args__c.(five), (#args__c.(six), #()))))))%V ⌝.


Definition to_val' (c : C) : val :=
  (#c.(one), (#c.(two), (#c.(three), (#c.(four), (#c.(five), (#c.(six), #())))))).

Definition from_val' (v : val) : option C :=
  match v with
  | (#(LitInt32 one), (#(LitInt32 two), (#(LitInt32 three), (#(LitInt four), (#(LitInt five), (#(LitInt six), #()))))))%V =>
    Some (mkC one two three four five six)
  | _ => None
  end.

#[global]
Instance completeInt_into_val : IntoVal C.
Proof.
  refine {|
    to_val := to_val';
    from_val := from_val';
    IntoVal_def := (mkC (W32 0) (W32 0) (W32 0) (W64 0) (W64 0) (W64 0))
  |}.
  intros v. 
  destruct v as [one two three four five six]; done.
Defined.

#[global]
Instance completeInt_into_val_for_type : IntoValForType C (struct.t completeint_gk.S).
Proof. constructor; auto 10. Defined.

Lemma own_to_val (v : val) (c : C) (dq : dfrac) :
  own v c dq -∗ ⌜ v = to_val c ⌝.
Proof.
  iIntros "%Hown_struct".
  
  subst. done.
Qed.


Lemma own_val_ty :
  ∀ (v : val) (x : C) (dq : dfrac), own v x dq -∗ ⌜val_ty v (struct.t completeint_gk.S)⌝.
Proof.
  iIntros (???) "Hown".
  unfold own. iNamed "Hown".
  
  iPureIntro.
  subst.
  repeat constructor.
Qed.

Lemma wp_Encode (args__v : val) (args__c : C) (pre_sl : Slice.t) (prefix : list u8) (dq : dfrac):
  {{{
        own args__v args__c dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    completeint_gk.Marshal (slice_val pre_sl) args__v
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

  wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  done.
Qed.

Lemma wp_Decode (enc : list u8) (enc_sl : Slice.t) (args__c : C) (suffix : list u8) (dq : dfrac):
  {{{
        ⌜ has_encoding enc args__c ⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    completeint_gk.Unmarshal (slice_val enc_sl)
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
  iIntros (l__one) "Hone". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__two) "Htwo". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__three) "Hthree". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__four) "Hfour". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__five) "Hfive". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__six) "Hsix". wp_pures.
  
  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (wp_ReadInt32 with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (wp_ReadInt32 with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (wp_ReadInt32 with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_load. wp_load. wp_load. wp_load. wp_load. wp_load. wp_load.
  wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
  iPureIntro. reflexivity.
Qed.

End completeInt.
End completeInt.

