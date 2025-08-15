From New.proof Require Import proof_prelude.
From New.proof Require Import github_com.tchajed.marshal.
From New.proof Require Import github_com.goose_lang.std.
From New.code Require Import github_com.mjschwenne.grackle.example.
From Grackle.pg Require Import github_com.mjschwenne.grackle.example.
From New.proof.github_com.goose_lang Require Import primitive.
From Perennial.Helpers Require Import NamedProps.

Module Person_Proof.
  Section Person_Proof.

    Context `{hG: heapGS Σ, !ffi_semantics _ _}.
    Context `{!globalsGS Σ} {go_ctx : GoContext}.

    Local Notation deps := (ltac2:(build_pkg_init_deps 'example) : iProp Σ) (only parsing).
    #[global]
    Program Instance : IsPkgInit example :=
      {|
        is_pkg_init_def := True;
        is_pkg_init_deps := deps;
      |}.

    Inductive Status :=
      | STATUS_UNSPECIFIED
      | STATUS_STUDENT
      | STATUS_STAFF
      | STATUS_PROFESSOR.

    Definition to_tag status : u64 :=
      match status with
      | STATUS_UNSPECIFIED => 0
      | STATUS_STUDENT => 1
      | STATUS_STAFF => 2
      | STATUS_PROFESSOR => 3
      end.

    Record C :=
      mkC {
        name' : go_string; 
        status' : Status;
      }.

    Definition has_encoding (encoded:list u8) (args:C) : Prop :=
      encoded = (u64_le $ length args.(name')) ++ args.(name') ++ (u64_le (to_tag args.(status')))
                                                               /\ length args.(name') < 2^64.
      
    Definition own (args__v:example.Person.t) (args__c:C) (dq:dfrac) : iProp Σ :=
      "%Hname" ∷ ⌜ args__v.(example.Person.Name') = args__c.(name') ⌝ ∗
      "%Hstatus" ∷ ⌜ args__v.(example.Person.Status') = (to_tag args__c.(status')) ⌝.

    Lemma wp_Enocde (args__t:example.Person.t) (args__c:C) (pre_sl:slice.t) (prefix:list u8) (dq:dfrac):
      {{{
            is_pkg_init example ∗
            own args__t args__c dq ∗
            own_slice pre_sl (DfracOwn 1) prefix ∗
            own_slice_cap w8 pre_sl (DfracOwn 1)
      }}}
        @! example.MarshalPerson #pre_sl #args__t
      {{{
            enc enc_sl, RET #enc_sl;
            ⌜ has_encoding enc args__c ⌝ ∗
            own args__t args__c dq ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl (DfracOwn 1)
      }}}.
      
    Proof.
      wp_start as "(@ & Hsl & Hcap)". wp_auto.

      wp_apply wp_AssumeNoStringOverflow.
      iIntros "%HnameLen". rewrite Hname in HnameLen. wp_auto.
      wp_apply wp_StringToBytes.
      iIntros (?) "Hname". wp_auto.

      wp_apply (wp_WriteLenPrefixedBytes with "[$Hsl $Hname $Hcap]").
      iIntros (?) "(Hsl & Hcap & Hname)". wp_auto.

      wp_apply (wp_WriteInt with "[$Hsl $Hcap]").
      iIntros (?) "[Hsl Hcap]". wp_auto.

      iApply "HΦ". iFrame.
      iSplit.
      + done.
      + rewrite -?app_assoc. rewrite Hname. rewrite Hstatus. iFrame.
        done.
    Qed.

    Lemma wp_Decode (enc: list u8) (enc_sl: slice.t) (args__c:C) (suffix: list u8) (dq: dfrac):
      {{{
            is_pkg_init example ∗
            own_slice enc_sl dq (enc ++ suffix) ∗
            ⌜ has_encoding enc args__c ⌝
      }}}
        @! example.UnmarshalPerson #enc_sl
      {{{
            args__t suff_sl, RET (#args__t, #suff_sl);
            own args__t args__c (DfracOwn 1) ∗
            own_slice suff_sl dq suffix
      }}}.

    Proof.
      wp_start as "(Hsl & %Henc)". wp_auto.
      unfold has_encoding in Henc.
      destruct Henc as [Henc HnameLen].
      rewrite Henc. rewrite -?app_assoc.

      wp_apply (wp_ReadLenPrefixedBytes with "[$Hsl]"); first word.
      iIntros (??) "[Hn Hsl]". wp_auto.

      wp_apply (wp_ReadInt with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_StringFromBytes with "[$Hn]").
      iIntros "Hn". wp_auto.

      iApply "HΦ". iFrame. done.
    Qed.
  End Person_Proof.
End Person_Proof.
