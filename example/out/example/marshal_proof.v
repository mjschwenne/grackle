From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import example.
From Perennial.program_proof Require Import marshal_stateless_proof.

Module encodeTimestamp.
Section encodeTimestamp.

Context `{!heapGS Σ}.

Record C :=
  mkC {
      hour : u32 ;
      minute : u32 ;
      second : u32 ;
    }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u32_le args.(hour)) ++ (u32_le args.(minute)) ++ (u32_le args.(second)).

Context `{!heapGS Σ}.

Definition own args_ptr args q : iProp Σ :=
  "Hargs_hour" ∷ args_ptr ↦[TimeStamp :: "hour"]{q} #args.(hour) ∗
  "Hargs_minute" ∷ args_ptr ↦[TimeStamp :: "minute"]{q} #args.(minute) ∗
  "Hargs_second" ∷ args_ptr ↦[TimeStamp :: "second"]{q} #args.(second).

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        own args_ptr args (DfracDiscarded)
  }}}
    TimeStamp__marshal #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) enc
  }}}.
Proof.
  iIntros (?) "H HΦ".
  wp_rec. wp_apply (wp_NewSlice).
  iIntros (?) "Hsl". wp_pures. wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT (DfracOwn 1) enc
  }}}
    UnmarshalTimeStamp (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args (DfracOwn 1)
  }}}.
Proof.
  Admitted.
