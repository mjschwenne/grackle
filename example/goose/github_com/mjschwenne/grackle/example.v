(* autogenerated from github.com/mjschwenne/grackle/example *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.

(* calendar.go *)

(* TimeStamp from timestamp.go *)

Definition TimeStamp := struct.decl [
  "hour" :: uint32T;
  "minute" :: uint32T;
  "second" :: uint32T
].

(* Event from event.go *)

Definition Event := struct.decl [
  "id" :: uint32T;
  "name" :: stringT;
  "startTime" :: struct.t TimeStamp;
  "endTime" :: struct.t TimeStamp
].

Definition Calendar := struct.decl [
  "events" :: slice.T (struct.t Event)
].

(* MarshalTimeStamp from timestamp.go *)

Definition MarshalTimeStamp: val :=
  rec: "MarshalTimeStamp" "t" "prefix" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.get TimeStamp "hour" "t"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.get TimeStamp "minute" "t"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.get TimeStamp "second" "t"));;
    ![slice.T byteT] "enc".

(* MarshalEvent from event.go *)

Definition MarshalEvent: val :=
  rec: "MarshalEvent" "e" "prefix" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.get Event "id" "e"));;
    let: "nameByte" := StringToBytes (struct.get Event "name" "e") in
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (slice.len "nameByte"));;
    "enc" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "enc") "nameByte");;
    "enc" <-[slice.T byteT] (MarshalTimeStamp (struct.get Event "startTime" "e") (![slice.T byteT] "enc"));;
    "enc" <-[slice.T byteT] (MarshalTimeStamp (struct.get Event "endTime" "e") (![slice.T byteT] "enc"));;
    ![slice.T byteT] "enc".

Definition MarshalCalendar: val :=
  rec: "MarshalCalendar" "c" "prefix" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (slice.len (struct.get Calendar "events" "c")));;
    "enc" <-[slice.T byteT] (marshal.WriteSlice (struct.t Event) (![slice.T byteT] "enc") (struct.get Calendar "events" "c") MarshalEvent);;
    ![slice.T byteT] "enc".

(* UnmarshalTimeStamp from timestamp.go *)

Definition UnmarshalTimeStamp: val :=
  rec: "UnmarshalTimeStamp" "s" :=
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: "hour" := ref (zero_val uint32T) in
    let: "minute" := ref (zero_val uint32T) in
    let: "second" := ref (zero_val uint32T) in
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    "hour" <-[uint32T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    "minute" <-[uint32T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    "second" <-[uint32T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    (struct.mk TimeStamp [
       "hour" ::= ![uint32T] "hour";
       "minute" ::= ![uint32T] "minute";
       "second" ::= ![uint32T] "second"
     ], ![slice.T byteT] "enc").

(* UnmarshalEvent from event.go *)

Definition UnmarshalEvent: val :=
  rec: "UnmarshalEvent" "s" :=
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: "id" := ref (zero_val uint32T) in
    let: "name" := ref (zero_val stringT) in
    let: "startTime" := ref (zero_val (struct.t TimeStamp)) in
    let: "endTime" := ref (zero_val (struct.t TimeStamp)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    "id" <-[uint32T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: "nameLen" := ref (zero_val uint64T) in
    let: "nameBytes" := ref (zero_val (slice.T byteT)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "nameLen" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadBytesCopy (![slice.T byteT] "enc") (![uint64T] "nameLen") in
    "nameBytes" <-[slice.T byteT] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    "name" <-[stringT] (StringFromBytes (![slice.T byteT] "nameBytes"));;
    let: ("0_ret", "1_ret") := UnmarshalTimeStamp (![slice.T byteT] "enc") in
    "startTime" <-[struct.t TimeStamp] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := UnmarshalTimeStamp (![slice.T byteT] "enc") in
    "endTime" <-[struct.t TimeStamp] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    (struct.mk Event [
       "id" ::= ![uint32T] "id";
       "name" ::= ![stringT] "name";
       "startTime" ::= ![struct.t TimeStamp] "startTime";
       "endTime" ::= ![struct.t TimeStamp] "endTime"
     ], ![slice.T byteT] "enc").

Definition UnmarshalCalendar: val :=
  rec: "UnmarshalCalendar" "s" :=
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: "events" := ref (zero_val (slice.T (struct.t Event))) in
    let: "eventsLen" := ref (zero_val uint64T) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "eventsLen" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadSlice (struct.t Event) (![slice.T byteT] "enc") (![uint64T] "eventsLen") UnmarshalEvent in
    "events" <-[slice.T (struct.t Event)] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    (struct.mk Calendar [
       "events" ::= ![slice.T (struct.t Event)] "events"
     ], ![slice.T byteT] "enc").

(* event.go *)

(* timestamp.go *)

End code.
