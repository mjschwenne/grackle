From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import example.
From Perennial.program_proof Require Import marshal_stateless_proof.

Module encodeTimestamp.
Section encodeTimestamp.

Context `{!heapGS Σ}.

(* Mirrors the structure of the TimeStamp struct in go. *)
Record C :=
  mkC {
      hour : u32 ;
      minute : u32 ;
      second : u32 ;
    }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  (* Definition of the marshaled struct as a tuple of little-edian values *)
  encoded = (u32_le args.(hour)) ++ (u32_le args.(minute)) ++ (u32_le args.(second)).

Context `{!heapGS Σ}.

Definition own args_ptr args q : iProp Σ :=
  (* Note tha the first '::' is actually \​Colon while the second one is two ':' characters *)

  (* A definition of the marshaled struct as a separation logic proposition asserting that
     - A field in args_ptr of type TimeStamp::hour with fractional ownership q has value #args.hour
     - A field in args_ptr of type TimeStamp::minute with ownership q has value #args.minute
     - A field in args_ptr of type TimeStamp:;second with ownership q has value #args.second
     Thus, this iProp encodes the existance of the struct, and the correctness of the values.
   *)
  "Hargs_hour" ∷ args_ptr ↦[TimeStamp :: "hour"]{q} #args.(hour) ∗
  "Hargs_minute" ∷ args_ptr ↦[TimeStamp :: "minute"]{q} #args.(minute) ∗
  "Hargs_second" ∷ args_ptr ↦[TimeStamp :: "second"]{q} #args.(second).

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        (* This pre-condition asserts that we have read access to a struct
           containing the values in `args'. *)
        own args_ptr args (DfracDiscarded)
  }}}
    MarshalTimeStamp #args_ptr
  {{{
        (* The post-condition asserts that the MarshalTimeStamp function returns
           an encoding `enc' such that the encoding mets the tuple
           interpretation of the encoding and that `enc' has the correct slice
           value `enc_sl'. *)
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) enc
  }}}.
Proof.
  (* Introduce the pre-condition has "H" and the weakest pre-condition for the
     post-condition as HΦ. *)
  iIntros (?) "H HΦ".
  (* Recall that `own' is a separating logic conjuction. Using the iNamed tactic
     we can destruct that into a hypothesis for each field in the struct. I
     believe that since we are using DfraceDiscarded (i.e. ϵ) for ownership, we
     can effectly treat this as a presistent hypothesis even though they stay in
     the spatial context. *)
  iNamed "H".
  (* β-reduction *)
  wp_rec.
  (* Create a new slice with a capacity of 12 bytes. *)
  wp_apply (wp_NewSliceWithCap).
  (* I'm not sure why I have to prove that 0 ≤ 12, but it's easy enough to prove
     that a non-negative integer is greater than or equal to zero. *)
  { apply encoding.unsigned_64_nonneg. }
  (* The goal starts with ∀ ptr : loc, so we have to introduce `ptr' of type
     location and that we own new slice of all zeros with 12 bytes which we just
     created with `wp_NewSliceWithCap'. *)
  iIntros (?) "Hsl".
  (* Creates a new pointer which points to the value described in the goal,
     `(slice.T byte.T) (Slice.mk ptr (W64 0) (W64 12))' *)
  wp_apply (wp_ref_to); first by val_ty. (* TODO Ask about `first by val_ty' *)
  (* The `wp_ref_to' creates an implication, ∀ l : loc, if l is a new, empty
     byte slice we can assign to `enc', so we introduce the Coq variable of type
     `loc' and an iris spatial hypothesis `Hptr' describing that new, empty
     value of `l'. *)
  iIntros (?) "Hptr".
  (* Pure reduction resolves the `let' clause. *)
  wp_pures.
  (* Now we have a sequence of 3 WriteInt32 statements writing values from the
     struct to the byte slice. First, we resolve loading the field from the
     struct. From Hargs_hour we know this value is #args.hour. *)
  wp_loadField.
  (* Load the value of the slice, the first argument of `marshal.WriteInt32'. *)
  wp_load.
  (* Creates an implication ∀ s' : slice with values starting with #args.hour, I
     think... *)
  wp_apply (wp_WriteInt32 with "[$]"). (* TODO Ask about `with "[$]"' *)
  (* Slurp up the new slice value starting with #args.hour as a hypothesis "Hsl"
     and place the slice in the Coq context. *)
  iIntros (?) "Hsl".
  (* Save the new slice s' to the encoding accumulator described by location
     `l'. *)
  wp_store.
  (* Repeat with minute field. *)
  wp_loadField. wp_load. wp_apply (wp_WriteInt32 with "[$]"). iIntros (?) "Hsl". wp_store.
  (* Repeat with second field. *)
  wp_loadField. wp_load. wp_apply (wp_WriteInt32 with "[$]"). iIntros (?) "Hsl". wp_store.
  (* Now we have location #l to a byte slice. We can load the slice. *)
  wp_load.
  (* We're done with the program analysis and have to show that Φ is true for
     s'1. Fortunately, HΦ is of the form post-condition -* Φ enc_sl so we can
     get the post-condition. *)
  iApply "HΦ".
  (* Now we apply the frame rule with "Hsl" to recover the explicit slice value. *)
  iFrame.
  (* With tactic we can convert an iris goal that's ⌜pure⌝ into just a regular
     Coq goal. *)
  iPureIntro.
  (* And the done tactic is an automatic solver capable to solving simple goals using
     - intros
     - reflexivity
     - symmetry
     - assumption
     - trivial
     - split
     - discriminate
     - contradiction *)
  done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        (* The pre-condition asserts that we have an encoding `enc' who can be
           interpreted as a tuple representation of the struct `args' that has a
           correct binary value `enc_sl' as per the `own' definition. *)
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT (DfracOwn 1) enc
  }}}
    UnmarshalTimeStamp (slice_val enc_sl)
  {{{
        (* The post-condition asserts that the return value `args_ptr' with has
           the correct values per the `own' definition. *)
        args_ptr, RET #args_ptr; own args_ptr args (DfracOwn 1)
  }}}.
Proof.
  (* Introduce `Henc' as a Coq proposition and Hsl as an iris proposition. The
     split mirrors the separating conjunction in the pre-condition. Like above,
     we also get HΦ to use with the post-condition. *)
  iIntros (?) "[%Henc Hsl] HΦ".
  (* β-reduction *)
  wp_rec.
  (* The `go` method starts by allocating a struct with three uint32. This
     produces another small subgoal which can be easily solved with `first by
     val_ty.' and then produces a implication about a new TimeStamp struct which
     is all zeros (the default value). *)
  wp_apply wp_allocStruct; first by val_ty.
  (* Introduce the location `l' and the premise of the implication (that there
     is a all-zero TimeStamp). *)
  iIntros (?) "Hs".
  (* Reduce the `let' *)
  wp_pures.
  (* Creates, as the premise of an implication, that there exists a location
     which points to `enc_sl' that we can reference with `"enc"'. *)
  wp_apply wp_ref_to; first done.
  (* Introduce the pointer created by wp_ref_to. *)
  iIntros (?) "Hptr".
  (* Reduce the `let'. *)
  wp_pures.
  (* Destruct "Hs" which asserts that there is an all-zero TimeStamp struct into
     a hypothesis "HH" asserting that we own a TimeStamp struct that's
     all-zero. *)
  iDestruct (struct_fields_split with "Hs") as "HH".
  (* Break down HH into three hypothesis, one for each of the fields in the
     struct. *)
  iNamed "HH".
  (* Recall that Henc asserts that ⌜has_encoding enc args⌝. This rewrites the
     `enc' in "Hsl" to the tuple from the has_encoding definition. *)
  rewrite Henc.
  (* Load the slice that we're going to use with ReadInt32. *)
  wp_load.
  (* Creates, as a premise, that after executing ReadInt32 we have a slice with
     just #args.minute and #args.second. *)
  wp_apply (wp_ReadInt32 with "[$]").
  (* Consume the premise that ReadInt32 just created. *)
  iIntros (?) "Hs".
  (* Simplify all of the directly nested `let' constructs. *)
  wp_pures.
  (* Write back to the struct *)
  wp_storeField.
  (* And then write that back to the encoding byte slice. *)
  wp_store.
  (* Repeat for the minute field *)
  wp_load. wp_apply (wp_ReadInt32 with "[$]"). iIntros (?) "Hs".
  wp_pures. wp_storeField. wp_store.
  (* Repeat for the second field *)
  wp_load. wp_apply (wp_ReadInt32 with "[$]"). iIntros (?) "Hs".
  wp_pures. wp_storeField. wp_store.
  (* Get the post-condition with HΦ. *)
  iApply "HΦ".
  (* TODO I know that this tactic is eliminating `|NC={⊤,⊤}⇒' but I'm not sure
     what this is representing. I think the NC might stand for 'No Context' or
     'New Context' but I don't have any real reason for that. *)
  iModIntro.
  (* The frame rule solves this bit by automatically expanding the `own'
     definition, which "hour", "minute" and "second" being joined via separating
     conjunction. This is trivially true, so we don't even need `done.' after
     this. *)
  iFrame.
Qed.
