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

    Definition status_has_encoding (encoded:list u8) (args:Status) : Prop :=
      encoded = u64_le $ to_tag $ args.

    Definition status_own (args__v: example.Status.t) (args__c:Status) (dq:dfrac) : iProp Σ :=
      "%Hstatus_eq" ∷ ⌜ args__v = to_tag args__c ⌝.

    Lemma wp_Status_Encode (args__t: example.Status.t) (args__c:Status) (pre_sl: slice.t) (prefix: list u8) (dq: dfrac):
      {{{
            is_pkg_init example ∗
            status_own args__t args__c dq ∗
            own_slice pre_sl (DfracOwn 1) prefix ∗
            own_slice_cap w8 pre_sl (DfracOwn 1)
      }}}
        @! example.MarshalStatus #pre_sl #args__t
      {{{
            enc enc_sl, RET #enc_sl;
            ⌜ status_has_encoding enc args__c ⌝ ∗
            status_own args__t args__c dq ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl (DfracOwn 1)
      }}}.

    Proof.
      wp_start as "(Hown & Hsl & Hcap)". unfold status_own. iNamed "Hown".
      wp_auto.

      wp_apply (wp_WriteInt with "[$Hsl $Hcap]").
      iIntros (?) "[Hsl Hcap]". wp_auto.

      iApply "HΦ". iFrame.
      iPureIntro. unfold status_has_encoding.
      rewrite Hstatus_eq.
      split; try reflexivity.
    Qed.

    Lemma wp_Status_Decode (enc: list u8) (enc_sl: slice.t) (args__c:Status) (suffix: list u8) (dq: dfrac):
      {{{
            is_pkg_init example ∗
            own_slice enc_sl dq (enc ++ suffix) ∗
            ⌜ status_has_encoding enc args__c ⌝
      }}}
        @! example.UnmarshalStatus #enc_sl
      {{{
            args__t suff_sl, RET (#args__t, #suff_sl);
            status_own args__t args__c (DfracOwn 1) ∗
            own_slice suff_sl dq suffix
      }}}.
    Proof.
      wp_start as "(Hsl & %Henc)". wp_auto.
      unfold status_has_encoding in Henc.
      rewrite Henc. 

      wp_apply (wp_ReadInt with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      iApply "HΦ".
      iFrame.
      done.
    Qed.

    Record C :=
      mkC {
        name' : go_string; 
        status' : Status;
        statuses' : list Status;
      }.

    Definition has_encoding (encoded:list u8) (args:C) : Prop :=
      ∃ (statuses_enc : list u8),
        encoded = (u64_le $ length args.(name')) ++ args.(name') ++ (u64_le (to_tag args.(status')))
                                                           ++ (u64_le $ length $ args.(statuses'))
                                                           ++ statuses_enc
        /\ encodes statuses_enc args.(statuses') status_has_encoding
        /\ length args.(name') < 2^64
        /\ length args.(statuses') < 2^64.
      
    Definition own (args__v:example.Person.t) (args__c:C) (dq:dfrac) : iProp Σ :=
      ∃ (l__statuses : list example.Status.t), 
      "%Hname" ∷ ⌜ args__v.(example.Person.Name') = args__c.(name') ⌝ ∗
      "%Hstatus" ∷ ⌜ args__v.(example.Person.Status') = (to_tag args__c.(status')) ⌝ ∗
      "Hown_statuses_sl" ∷ own_slice args__v.(example.Person.Statuses') dq l__statuses ∗
      "Hown_statuses_own" ∷ ([∗ list] x;c ∈ l__statuses;args__c.(statuses'), status_own x c dq) ∗
      "%Hown_statuses_len" ∷ ⌜ length l__statuses < 2^64 ⌝.

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

      wp_apply (wp_WriteInt with "[$Hsl $Hcap]").
      iIntros (?) "[Hsl Hcap]". wp_auto.

      iDestruct (own_slice_len with "Hown_statuses_sl") as "%Hown_statuses_sz".
      iDestruct (big_sepL2_length with "Hown_statuses_own") as "%Hown_statuses_sz'".
      rewrite Hown_statuses_sz' in Hown_statuses_sz.
      wp_apply (wp_WriteSlice with "[$Hsl $Hcap $Hown_statuses_sl $Hown_statuses_own]").
      {
        iIntros (????) "!>".
        iIntros (?) "(Hown & Hsl & Hcap) HΦ".
        wp_apply (wp_Status_Encode with "[$Hown $Hsl $Hcap]").
        iApply "HΦ".
      }
      iIntros (statuses_enc statuses_sl') "(Hown_statuses & Hown_statuses_own & %Henc_statuses & Hsl & Hcap)".
      wp_auto.

      iApply "HΦ". rewrite -?app_assoc.
      iFrame. iPureIntro.

      unfold has_encoding.
      split; last done.
      exists statuses_enc.
      split.
      {
        rewrite Hown_statuses_sz.
        rewrite ?w64_to_nat_id.
        congruence.
      }
      rewrite <- Hown_statuses_sz'.
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
      destruct Henc as (statuses_enc & Henc & Hstatuses_enc & HnameLen & HstatusesLen).
      rewrite Henc. rewrite -?app_assoc.

      wp_apply (wp_ReadLenPrefixedBytes with "[$Hsl]"); first word.
      iIntros (??) "[Hn Hsl]". wp_auto.

      wp_apply (wp_ReadInt with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_ReadInt with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_ReadSlice  with "[$Hsl]").
      {
        iSplit; auto.
        iSplit; first word.
        iIntros (????) "!>".
        iIntros (?) "[Hsl Henc] HΦ".
        wp_apply (wp_Status_Decode with "[$Hsl $Henc]").
        iApply "HΦ".
      }
      iIntros (???) "(Hown_statuses_sl & Hown_statuses_own & Hsl)". wp_auto.
      iDestruct (big_sepL2_length with "Hown_statuses_own") as "%Hown_statuses_sz".
      rewrite <- Hown_statuses_sz in HstatusesLen.
      
      wp_apply (wp_StringFromBytes with "[$Hn]").
      iIntros "Hn". wp_auto.

      iApply "HΦ". iFrame. done.
    Qed.
  End Person_Proof.
End Person_Proof.
