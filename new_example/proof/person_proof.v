From New.proof Require Import proof_prelude.
From New.proof Require Import github_com.tchajed.marshal.
From New.proof Require Import github_com.goose_lang.std.
From New.code Require Import github_com.mjschwenne.grackle.new_example.
From Grackle.pg Require Import github_com.mjschwenne.grackle.new_example.

Module Person_Proof.
  Section Status_Proof.

    Context `{hG: heapGS Σ, !ffi_semantics _ _}.
    Context `{!goGlobalsGS Σ}.

    #[global]
      Program Instance : IsPkgInit main :=
      ltac2:(build_pkg_init ()).

    Inductive V :=
      | STATUS_UNSPECIFIED
      | STATUS_STUDENT
      | STATUS_STAFF
      | STATUS_PROFESSOR.

    Definition to_tag (status:V) : u64 :=
      match status with
      | STATUS_UNSPECIFIED => 0
      | STATUS_STUDENT => 1
      | STATUS_STAFF => 2
      | STATUS_PROFESSOR => 3
      end.

    Definition to_v (status:V) := #(to_tag status).

    Record C :=
      mkC {
        status' : V;
      }.

    Definition has_encoding (encoded:list u8) (args:C) : Prop :=
      encoded = (u64_le (to_tag args.(status'))).
      
    Definition own (args__v:main.Person_Status.t) (args__c:C) (dq:dfrac) : iProp Σ :=
      "%Hstatus" ∷ ⌜ args__v.(main.Person_Status.status') = (to_tag args__c.(status')) ⌝.

    Lemma wp_GetStatus (args__t:main.Person_Status.t) (args__c:C) (dq:dfrac):
      {{{
            is_pkg_init main ∗
            own args__t args__c dq
      }}}
        args__t @ main @ "Person_Status" @ "GetStatus" #()
      {{{
            status, RET #status;
            ⌜ status = (to_tag args__c.(status')) ⌝ ∗
            own args__t args__c dq
      }}}.

    Proof.
      wp_start as "Hown". wp_auto.
      iDestruct "Hown" as "%Hown".
      iApply "HΦ".
      iSplitR; first done.
      done.
    Qed.

    Lemma wp_SetStatus (args__t:main.Person_Status.t) (args__c:C) new (dq:dfrac):
      {{{
            is_pkg_init main
      }}}
        args__t @ main @ "Person_Status" @ "SetStatus" #new
      {{{
            RET #();
            ⌜ args__t.(main.Person_Status.status') = new ⌝ ∗
            own args__t args__c dq
      }}}.

    Proof.
      wp_start. wp_auto.
      wp_if_destruct.
      + wp_auto. iApply "HΦ".
        iSplitL.
    Admitted.
      
    Lemma wp_Enocde (args__t:main.Person_Status.t) (args__c:C) (pre_sl:slice.t) (prefix:list u8) (dq:dfrac):
      {{{
            is_pkg_init main ∗
            own args__t args__c dq ∗
            own_slice pre_sl (DfracOwn 1) prefix ∗
            own_slice_cap w8 pre_sl (DfracOwn 1)
      }}}
        main @ "MarshalPersonStatus" #pre_sl #args__t
      {{{
            enc enc_sl, RET #enc_sl;
            ⌜ has_encoding enc args__c ⌝ ∗
            own args__t args__c dq ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl (DfracOwn 1)
      }}}.
      
    Proof.
      wp_start as "(Hown & Hsl & Hcap)". wp_auto.
      iDestruct "Hown" as "%Hown_status".

      wp_apply (wp_WriteInt with "[$Hsl $Hcap]").
      iIntros (?) "[Hsl Hcap]". wp_auto.

      iApply "HΦ". iFrame.
      iSplit.
      + iPureIntro. unfold has_encoding. rewrite Hown_status. reflexivity.
      + done.
    Qed.

    Lemma wp_Decode (enc: list u8) (enc_sl: slice.t) (args__c:C) (suffix: list u8) (dq: dfrac):
      {{{
            is_pkg_init main ∗
            own_slice enc_sl dq (enc ++ suffix) ∗
            ⌜ has_encoding enc args__c ⌝
      }}}
        main @ "UnmarshalPersonStatus" #enc_sl
      {{{
            args__t suff_sl, RET (#args__t, #suff_sl);
            own args__t args__c (DfracOwn 1) ∗
            own_slice suff_sl dq suffix
      }}}.

    Proof.
      wp_start as "(Hsl & %Henc)". wp_auto.
      unfold has_encoding in Henc.
      rewrite Henc.

      wp_apply (wp_ReadInt with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_SetStatus with "[status]").
      iIntros "[%Hstatus Hown]". wp_auto.
    Admitted.
  End Status_Proof.
End Person_Proof.
