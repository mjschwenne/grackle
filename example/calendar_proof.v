From Perennial.program_proof Require Import grove_prelude.
From Grackle.example Require Import goose.github_com.mjschwenne.grackle.example.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Grackle.example Require Import event_proof.
From Perennial.goose_lang Require Import lib.slice.pred_slice.

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
      | e :: tail => ∃ (e_enc tail_enc:list u8), encoding = e_enc ++ tail_enc /\
                                               Event.has_encoding e_enc e /\
                                               has_events_encoding tail_enc tail
      end.

    Definition has_encoding (encoded:list u8) (args:C) : Prop :=
      ∃ (events_enc : list u8),
        encoded = (u64_le $ length $ args.(events)) ++ events_enc /\
        has_events_encoding events_enc args.(events).
    
    Definition own (args__v : val) (args__c : C) (dq :dfrac) : iProp Σ :=
      ∃ (events__sl : Slice.t),
        "%Hown_struct" ∷ ⌜ args__v = ((slice_val events__sl), #())%V ⌝ ∗
        (* FIXME: That `ty' is wrong. How to I get an EventT? *)
        "Hown_events" ∷ is_pred_slice Event.own events__sl byteT dq args__c.(events).
    
  End Calendar.
End Calendar.
    
