From Perennial.program_proof Require Import grove_prelude.
From New.proof Require Import proof_prelude.
From Grackle.new_ex Require Import goose.github_com.mjschwenne.grackle.new_example.
From Grackle.new_ex Require Import pg.github_com.mjschwenne.grackle.new_example.

Module TimeStamp_Proof.
  Section TimeStamp_Proof.

    Context `{ffi_syntax}.
    Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.

    Definition has_encoding (encoded:list u8) (args:main.TimeStamp.t) : Prop :=
      encoded = (u32_le args.(main.TimeStamp.hour')) ++ (u32_le args.(main.TimeStamp.minute'))
                  ++ (u32_le args.(main.TimeStamp.second')).

    Definition own (args__v : val) (args__c : main.TimeStamp.t) (dq : dfrac) : iProp Σ :=
      "%Hown_struct" ∷ ⌜ args__v = (#args__c.(main.TimeStamp.hour'), (#args__c.(main.TimeStamp.minute'),
                                                                    (#args__c.(main.TimeStamp.second'), #())))%V ⌝.

    Lemma wp_Encode (args__v : val) (args__c : main.TimeStamp.t) (pre_sl : slice.t) (prefix : list u8) (dq : dfrac):
      {{{
            own args__v args__c dq ∗
            own_slice pre_sl (DfracOwn 1) prefix
      }}}
        main.MarshalTimeStamp #pre_sl args__v
      {{{
            enc enc_sl, RET #();
            ⌜ has_encoding enc args__c ⌝ ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own args__v args__c dq
      }}}.

      Proof. 
        wp_start as "H". iDestruct "H" as "[Hown Hsl]".
        wp_rec. wp_auto.
      Admitted.
  End TimeStamp_Proof.
End TimeStamp_Proof.
