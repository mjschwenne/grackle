(* autogenerated from example/test *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.

(* event.go *)

Definition Event := struct.decl [
  "id" :: uint32T;
  "startTime" :: ptrT;
  "endTime" :: ptrT
].

Definition Event__approxSize: val :=
  rec: "Event__approxSize" "e" :=
    #0.

(* TimeStamp from timestamp.go *)

Definition TimeStamp := struct.decl [
  "hour" :: uint32T;
  "minute" :: uint32T;
  "second" :: uint32T
].

Definition MarshalTimeStamp: val :=
  rec: "MarshalTimeStamp" "t" "prefix" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.loadF TimeStamp "hour" "t"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.loadF TimeStamp "minute" "t"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.loadF TimeStamp "second" "t"));;
    ![slice.T byteT] "enc".

Definition MarshalEvent: val :=
  rec: "MarshalEvent" "e" "prefix" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.loadF Event "id" "e"));;
    "enc" <-[slice.T byteT] (MarshalTimeStamp (struct.loadF Event "startTime" "e") (![slice.T byteT] "enc"));;
    "enc" <-[slice.T byteT] (MarshalTimeStamp (struct.loadF Event "endTime" "e") (![slice.T byteT] "enc"));;
    ![slice.T byteT] "enc".

Definition UnmarshalTimeStamp: val :=
  rec: "UnmarshalTimeStamp" "s" :=
    let: "t" := struct.alloc TimeStamp (zero_val (struct.t TimeStamp)) in
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    struct.storeF TimeStamp "hour" "t" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    struct.storeF TimeStamp "minute" "t" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    struct.storeF TimeStamp "second" "t" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    ("t", ![slice.T byteT] "enc").

Definition UnmarshalEvent: val :=
  rec: "UnmarshalEvent" "s" :=
    let: "e" := struct.alloc Event (zero_val (struct.t Event)) in
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    struct.storeF Event "id" "e" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := UnmarshalTimeStamp (![slice.T byteT] "enc") in
    struct.storeF Event "startTime" "e" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := UnmarshalTimeStamp (![slice.T byteT] "enc") in
    struct.storeF Event "endTime" "e" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    ("e", ![slice.T byteT] "enc").

(* timestamp.go *)

Definition TimeStamp__approxSize: val :=
  rec: "TimeStamp__approxSize" "t" :=
    #0.

End code.
