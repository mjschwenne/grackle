From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import goose.github_com.mjschwenne.grackle.example.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Grackle.example Require Import event_proof.

Module Calendar.
  Section Calendar.

    Context `{!heapGS Σ}.

    Record C :=
      mkC {
          events : list Event.C;
        }.

    Fixpoint has_events_encoding (encoding:list u8) (events: list Event.C) : Prop :=
      match events with
      | [] => True
      | e :: tail => ∃ (e_enc tail_enc:list u8), Event.has_encoding e_enc e /\
                                                has_events_encoding tail_enc tail
      end.

    Definition has_encoding (encoded:list u8) (args:C) : Prop :=
      ∃ (events_enc : list u8),
        encoded = (u64_le $ length $ args.(events)) ++ events_enc /\
        has_events_encoding events_enc args.(events).
    
  End Calendar.
End Calendar.
    
