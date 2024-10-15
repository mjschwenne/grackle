(* autogenerated from github.com/mjschwenne/grackle/test/event *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mjschwenne.grackle.test.timestamp.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.

Definition Event := struct.decl [
  "id" :: uint32T;
  "startTime" :: ptrT;
  "endTime" :: ptrT
].

Definition Event__approxSize: val :=
  rec: "Event__approxSize" "e" :=
    #0.

Definition MarshalEvent: val :=
  rec: "MarshalEvent" "e" "prefix" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.loadF Event "id" "e"));;
    "enc" <-[slice.T byteT] (TimeStamp_gk.MarshalTimeStamp (struct.loadF Event "startTime" "e") (![slice.T byteT] "enc"));;
    "enc" <-[slice.T byteT] (TimeStamp_gk.MarshalTimeStamp (struct.loadF Event "endTime" "e") (![slice.T byteT] "enc"));;
    ![slice.T byteT] "enc".

Definition UnmarshalEvent: val :=
  rec: "UnmarshalEvent" "s" :=
    let: "e" := struct.alloc Event (zero_val (struct.t Event)) in
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    struct.storeF Event "id" "e" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := TimeStamp_gk.UnmarshalTimeStamp (![slice.T byteT] "enc") in
    struct.storeF Event "startTime" "e" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := TimeStamp_gk.UnmarshalTimeStamp (![slice.T byteT] "enc") in
    struct.storeF Event "endTime" "e" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    ("e", ![slice.T byteT] "enc").

End code.
