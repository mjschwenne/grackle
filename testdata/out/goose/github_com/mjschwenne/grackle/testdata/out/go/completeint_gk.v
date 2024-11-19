(* autogenerated from github.com/mjschwenne/grackle/testdata/out/go/completeint_gk *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.

Definition S := struct.decl [
  "One" :: uint32T;
  "Two" :: uint32T;
  "Three" :: uint32T;
  "Four" :: uint64T;
  "Five" :: uint64T;
  "Six" :: uint64T
].

Definition S__approxSize: val :=
  rec: "S__approxSize" "c" :=
    #0.

Definition Marshal: val :=
  rec: "Marshal" "c" "prefix" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.loadF S "One" "c"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.loadF S "Two" "c"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt32 (![slice.T byteT] "enc") (struct.loadF S "Three" "c"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF S "Four" "c"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF S "Five" "c"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF S "Six" "c"));;
    ![slice.T byteT] "enc".

Definition Unmarshal: val :=
  rec: "Unmarshal" "s" :=
    let: "c" := struct.alloc S (zero_val (struct.t S)) in
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    struct.storeF S "One" "c" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    struct.storeF S "Two" "c" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt32 (![slice.T byteT] "enc") in
    struct.storeF S "Three" "c" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF S "Four" "c" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF S "Five" "c" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF S "Six" "c" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    ("c", ![slice.T byteT] "enc").

End code.
