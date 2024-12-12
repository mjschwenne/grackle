From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import goose.github_com.mjschwenne.grackle.example.
From Perennial.program_proof Require Import marshal_stateless_proof.

(* Annotations and discussion for this file is in timestamp_proof.org *)

Module TimeStamp.
Section TimeStamp.

Context `{!heapGS Σ}.

Record C :=
  mkC {
      hour : u32 ;
      minute : u32 ;
      second : u32 ;
    }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u32_le args.(hour)) ++ (u32_le args.(minute)) ++ (u32_le args.(second)).

Definition own (args__v : val) (args__c : C) (dq : dfrac) : iProp Σ :=
  "%Hown_struct" ∷ ⌜ args__v = (#args__c.(hour), (#args__c.(minute), (#args__c.(second), #())))%V ⌝.

Lemma wp_Encode (args__v : val) (args__c : C) (pre_sl : Slice.t) (prefix : list u8) (dq : dfrac):
  {{{
        own args__v args__c dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    MarshalTimeStamp args__v (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜ has_encoding enc args__c ⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc) ∗
        own args__v args__c dq
  }}}.
Proof.
  iIntros (?) "H HΦ". iDestruct "H" as "[Hown Hsl]". iNamed "Hown".
  wp_rec. wp_pures. iUnfold own in "Hown". iNamed "Hown". rewrite Hown_struct.
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr".
  wp_pures.

  wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. wp_apply (wp_WriteInt32 with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc. iFrame.
  iPureIntro. done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) (suffix : list u8) (q : dfrac):
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT q (enc ++ suffix)
  }}}
    UnmarshalTimeStamp (slice_val enc_sl)
  {{{
        args_v suff_sl, RET (args_v, suff_sl); own args_v args (DfracOwn 1) ∗
                                                    own_slice_small suff_sl byteT q suffix
  }}}.

Proof.
  iIntros (?) "[%Henc Hsl] HΦ". wp_rec.
  wp_apply wp_ref_to; first done.
  iIntros (ls) "Hs". wp_pures.

  wp_apply wp_ref_of_zero; first done.
  iIntros (l__hour) "Hhour". wp_pures.

  wp_apply wp_ref_of_zero; first done.
  iIntros (l__minute) "Hminute". wp_pures.

  wp_apply wp_ref_of_zero; first done.
  iIntros (l__second) "Hsecond". wp_pures.

  unfold has_encoding in Henc. rewrite Henc.

  wp_load. wp_apply (wp_ReadInt32 with "[$]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (wp_ReadInt32 with "[$]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_load. wp_apply (wp_ReadInt32 with "[$]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_load. wp_load. wp_load. wp_load. wp_pures. iApply "HΦ". iModIntro. iFrame.
  unfold own. iPureIntro. reflexivity.
Qed.

End TimeStamp.
End TimeStamp.
