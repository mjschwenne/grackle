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

    (*
       I could flatten this own and require the caller to pass each "predslice"
       individually to wp_Encode.
     *)
    Record C := mkC {
       hash : list u8;
       events : list Event_Proof.C; 
      }.

    Definition has_encoding (encoded:list u8) (args__c:C) : Prop :=
      ∃ (events__enc : list u8),
        encoded = (u64_le $ length args__c.(hash)) ++ args__c.(hash) ++
                                                            (u64_le $ length args__c.(events)) ++ events__enc /\
        encodes events__enc args__c.(events) Event_Proof.has_encoding /\
        length args__c.(hash) < 2^64 /\
        length args__c.(events) < 2^64.

    Definition own (v:main.Calendar.t) (c:C) (dq:dfrac) : iProp Σ :=
      ∃ (e:list main.Event.t),
        "Hown_hash" ∷ own_slice v.(main.Calendar.hash') dq c.(hash) ∗
        "Hown_events_sl" ∷ own_slice v.(main.Calendar.events') dq e ∗
        "Hown_events_own" ∷ [∗ list] x;s ∈ e;c.(events), Event_Proof.own x s dq.

    Lemma wp_Encode (args__t:main.Calendar.t) (args__c:C) (pre_sl:slice.t) (prefix:list u8) (dq:dfrac) :
      length args__c.(hash) < 2^64 ->
      length args__c.(events) < 2^64 ->
      {{{
            is_pkg_init main ∗
            own args__t args__c dq ∗
            own_slice pre_sl (DfracOwn 1) prefix ∗
            own_slice_cap w8 pre_sl 
      }}}
        main @ "MarshalCalendar" #pre_sl #args__t
      {{{
            enc enc_sl, RET #enc_sl;
            ⌜ has_encoding enc args__c ⌝ ∗
            own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
            own_slice_cap w8 enc_sl
      }}}.

      Proof.
        intros HhashLen HeventsLen.
        wp_start as "(Hown & Hsl & Hcap)". iNamed "Hown". wp_auto.

        wp_apply (wp_WriteLenPrefixedBytes with "[$Hsl $Hcap $Hown_hash]").
        iIntros (?) "(Hsl & Hcap & Hown_hash)". wp_auto. 
        
        wp_apply (wp_WriteInt with "[$Hsl $Hcap]").
        iIntros (?) "[Hsl Hcap]". wp_auto.

        iDestruct (own_slice_len with "Hown_events_sl") as "%Hown_events_sz".
        iDestruct (big_sepL2_length with "Hown_events_own") as "%Hown_events_length".
        rewrite Hown_events_length in Hown_events_sz.
        wp_apply (wp_WriteSlice with "[$Hsl $Hown_events_sl $Hown_events_own]"). 
        {
          iIntros (????) "!>".
          iIntros (?) "[Hsl Hcap] HΦ".
          wp_apply (Event_Proof.wp_Encode with "[$Hsl $Hcap]").
          iApply "HΦ".
        }
        iIntros (??) "(Hevents & %HeventsEnc & Hsl)". wp_auto.

        iApply "HΦ". rewrite -?app_assoc. iFrame.
        iPureIntro. unfold has_encoding.
        exists enc. split.
        {
          rewrite Hown_events_sz.
          rewrite ?w64_to_nat_id.
          done.
        } done.
    Qed.

    Lemma wp_Decode (enc:list u8) (enc_sl:slice.t) (args__c:C) (suffix:list u8) (dq: dfrac):
      {{{
            is_pkg_init main ∗
            own_slice enc_sl dq (enc ++ suffix) ∗
            ⌜ has_encoding enc args__c ⌝
      }}}     
        main @ "UnmarshalCalendar" #enc_sl
      {{{
            suff_sl args__t (events:list main.Event.t), RET (#args__t, #suff_sl);
            own_slice suff_sl dq suffix ∗
            own_slice args__t.(main.Calendar.events') (DfracOwn 1) events
      }}}.
    Proof.
      wp_start as "[Hsl %Henc]". wp_auto.
      unfold has_encoding in Henc.
      destruct Henc as (events__enc & Henc & HeventsEncodes & HhashLen & HeventsLen).
      rewrite Henc. rewrite -?app_assoc.

      wp_apply (wp_ReadLenPrefixedBytes with "[$Hsl]"); first word.
      iIntros (??) "[Hhash Hsl]". wp_auto. 
      
      wp_apply (wp_ReadInt with "[$Hsl]").
      iIntros (?) "Hsl". wp_auto.

      wp_apply (wp_ReadSlice _ _ args__c.(Calendar_Proof.events) with "[$Hsl]").
      {
        iSplit; auto.
        iSplit; first word.
        iIntros (????) "!>".
        iIntros (?) "[Hsl' Henc'] HΦ".
        wp_apply (Event_Proof.wp_Decode with "[$Hsl' $Henc']").
        iApply "HΦ".
      } 
      iIntros (???) "(Hevent & HeventPred & Hsl)". wp_auto.

      iApply "HΦ". iFrame.
    Qed.
  End Calendar_Proof.
End Calendar_Proof.
    
