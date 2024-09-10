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
      startTime : encodeTimestamp.Timestamp ;
      endTime : encodeTimestamp.Timestamp ;
    }.

Definition has_encoding (encoded:list u8) (args:EventStruct) : Prop :=
  ∃ start_enc end_enc,
  encoded = (u32_le args.(id)) ++ start_enc ++ end_enc
  /\ encodeTimestamp.has_encoding start_enc args.(startTime)
  /\ encodeTimestamp.has_encoding end_enc args.(endTime).

Definition own args_ptr args q : iProp Σ :=
  ∃ start_enc end_enc,
  "Hargs_id" ∷ args_ptr ↦[Event :: "id"]{q} #args.(id) ∗
  (* So, I think the problem with this definition is that start_enc isn't
     related to a timestamp... *)
  "Hargs_start" ∷ args_ptr ↦[Event :: "start"]{q} start_enc ∗
  "Hargs_start_enc" ∷ encodeTimestamp.own (args_ptr +ₗ 4) args.(startTime) q ∗
  "Hargs_end" ∷ args_ptr ↦[Event :: "end"]{q} end_enc ∗
  "Hargs_end_enc" ∷ encodeTimestamp.own (args_ptr +ₗ 16) args.(endTime) q.

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

  wp_loadField.
  (* wp_apply (encodeTimestamp.wp_Encode (args_ptr +ₗ 4) args.(startTime) Φ with "[Hargs_start Hargs_start_enc]"). *)
Abort.

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
  Abort.

End encodeEvent.
End encodeEvent.
