From New.proof Require Import proof_prelude.
From Grackle.new_ex Require Import goose.github_com.mjschwenne.grackle.new_example.
From Grackle.new_ex Require Import pg.github_com.mjschwenne.grackle.new_example.
From New.proof Require Import github_com.tchajed.marshal.
From Grackle.new_ex Require Import event_proof.

Module Calendar_Proof.
  Section Calendar_Proof.

    Context `{hG: heapGS Σ, !ffi_semantics _ _}.
    Context `{!goGlobalsGS Σ}.

    #[global]
      Program Instance : IsPkgInit main :=
        ltac2:(build_pkg_init ()).

    (* TODO: Figure out the impacts of not having pred_slice ported. *)
    Definition has_encoding (encoded:list u8) (args:main.Calendar.t) : Prop :=
      ∃ (events : list main.Event.t) (events__enc : list u8),
        encoded = (u64_le $ args.(main.Calendar.events').(slice.len_f)) ++ events__enc /\
        encodes events__enc events Event_Proof.has_encoding /\
        length events < 2^64.

    Lemma wp_Encode (args__c:main.Calendar.t) (pre_sl:slice.t) (prefix:list u8) (dq:dfrac):
      uint.nat args__c.(main.Calendar.events').(slice.len_f) < 2^64 ->
      {{{
            is_pkg_init main ∗
            own_slice pre_sl (DfracOwn 1) prefix ∗
            own_slice_cap w8 pre_sl 
      }}}
        main @ "MarshalCalendar" #pre_sl #args__c
      {{{
            enc enc_sl, RET #enc_sl;
            ⌜ has_encoding enc args__c ⌝ ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl
      }}}.

      Proof.
      Admitted.
  End Calendar_Proof.
End Calendar_Proof.
    
