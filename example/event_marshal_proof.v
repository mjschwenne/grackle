From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import example.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Grackle.example Require Import marshal_proof.

Module encodeEvent.
Section encodeEvent.

Context `{!heapGS Σ}.

Record EventStruct :=
  mkC {
      id : u32 ;
      startTime : list u8 ;
      endTime : list u8 ;
    }.

Definition has_encoding (encoded:list u8) (args:EventStruct) : Prop :=
  encoded = (u32_le args.(id)) ++ args.(startTime) ++ args.(endTime).

Definition own args_ptr args q : iProp Σ :=
  ∃ start_sl end_sl,
  "Hargs_id" ∷ args_ptr ↦[Event :: "id"]{q} #args.(id) ∗
  "Hargs_start" ∷ args_ptr ↦[Event :: "startTime"]{q} (slice_val start_sl) ∗
  "Hargs_start_sl" ∷ own_slice_small start_sl byteT q args.(startTime) ∗
  "Hargs_end" ∷ args_ptr ↦[Event :: "endTime"]{q} (slice_val end_sl) ∗
  "Hargs_end_sl" ∷ own_slice_small end_sl byteT q args.(endTime).

Lemma wp_Encode (args_ptr:loc) (args:EventStruct) :
  {{{
        own args_ptr args (DfracDiscarded)
  }}}
    MarshalEvent #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) enc
  }}}.
Proof.
  iIntros (?) "H HΦ". iNamed "H". wp_rec.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hsl".
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr".
  wp_pures.

  wp_loadField. wp_load. wp_apply (wp_WriteInt32 with "[$]").
  iIntros (?) "Hsl". wp_store.

  wp_apply (wp_struct_fieldRef_pointsto). { simpl. Admitted.

Lemma wp_Decode enc enc_sl (args:EventStruct) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT (DfracOwn 1) enc
  }}}
    UnmarshalEvent (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args (DfracOwn 1)
  }}}.
Proof.
  Admitted.

End encodeEvent.
End encodeEvent.
