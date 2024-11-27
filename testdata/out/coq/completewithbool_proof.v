From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completewithbool_gk.
From Grackle.test Require Import completemessage_proof.
From Goose Require Import github_com.mjschwenne.grackle.testdata.out.go.completemessage_gk.

Module completeWithBool.
Section completeWithBool.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        msg : completeMessage.C;
        success : bool;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  ∃ (msg_enc : list u8), 
  encoded = msg_enc ++
              [if args.(success) then W8 1 else W8 0]
  /\ completeMessage.has_encoding msg_enc args.(msg).

Definition own (args_ptr: loc) (args: C) (dq: dfrac) : iProp Σ :=
  ∃ (msg_l : loc) , 
  "Hargs_msg" ∷ args_ptr ↦[completewithbool_gk.S :: "Msg"]{dq} #msg_l ∗
  "Hargs_msg_enc" ∷ completeMessage.own msg_l args.(msg) dq ∗
  "Hargs_success" ∷ args_ptr ↦[completewithbool_gk.S :: "Success"]{dq} #args.(success).

Lemma wp_Encode (args_ptr:loc) (args:C) (pre_sl:Slice.t) (prefix:list u8) (dq: dfrac):
  {{{
        own args_ptr args dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    completewithbool_gk.Marshal #args_ptr (slice_val pre_sl)
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

  wp_loadField. wp_apply (wp_Assume). iIntros "%Hmsg_nn".
  wp_load. wp_loadField.
  wp_apply (completeMessage.wp_Encode with "[$Hargs_msg_enc $Hsl]").
  iIntros (msg_enc msg_sl) "(%Hargs_msg_enc & Hargs_msg_own & Hsl)".
  wp_store.

  wp_loadField. wp_load. wp_apply (wp_WriteBool with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. exists msg_enc. 
  split.
  { rewrite ?string_bytes_length.
  rewrite ?w64_to_nat_id. exact.
  } { exact. }
Qed.

Lemma wp_Decode enc enc_sl (args: C) (suffix: list u8) (dq: dfrac):
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    completewithbool_gk.Unmarshal (slice_val enc_sl)
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
  destruct Henc as ( msg_sl & Henc & Hencoding_msg ).
  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (completeMessage.wp_Decode msg_sl with "[Hsl]").
  { iFrame. exact. } iIntros (??) "[Hmsg Hsl]". wp_pures. wp_storeField. wp_store.

  wp_load. wp_apply (wp_ReadBool with "[Hsl]").
  { simpl. iFrame. }
  iIntros (success_b ?) "[%Hsuccess Hsl]".
  assert (success_b = args.(success)) as Hargs_success.
  { destruct args.(success); rewrite Hsuccess; reflexivity. }
  rewrite Hargs_success.
  wp_pures. wp_storeField. wp_store.

  wp_load. wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
Qed.

End completeWithBool.
End completeWithBool.

