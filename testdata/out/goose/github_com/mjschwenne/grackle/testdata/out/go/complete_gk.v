(* autogenerated from github.com/mjschwenne/grackle/testdata/out/go/complete_gk *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mjschwenne.grackle.testdata.out.go.completeint_gk.
From Goose Require github_com.mjschwenne.grackle.testdata.out.go.completeslice_gk.
From Goose Require github_com.mjschwenne.grackle.testdata.out.go.structslice_gk.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.

Definition S := struct.decl [
  "Int" :: struct.t completeint_gk.S;
  "Slc" :: struct.t completeslice_gk.S;
  "Success" :: boolT;
  "Sslice" :: slice.T (struct.t structslice_gk.S);
  "Iints" :: slice.T uint64T
].

Definition Marshal: val :=
  rec: "Marshal" "prefix" "c" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (completeint_gk.Marshal (![slice.T byteT] "enc") (struct.get S "Int" "c"));;
    "enc" <-[slice.T byteT] (completeslice_gk.Marshal (![slice.T byteT] "enc") (struct.get S "Slc" "c"));;
    "enc" <-[slice.T byteT] (marshal.WriteBool (![slice.T byteT] "enc") (struct.get S "Success" "c"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (slice.len (struct.get S "Sslice" "c")));;
    "enc" <-[slice.T byteT] (marshal.WriteSlice (struct.t structslice_gk.S) (![slice.T byteT] "enc") (struct.get S "Sslice" "c") structslice_gk.Marshal);;
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (slice.len (struct.get S "Iints" "c")));;
    "enc" <-[slice.T byteT] (marshal.WriteSlice uint64T (![slice.T byteT] "enc") (struct.get S "Iints" "c") marshal.WriteInt);;
    ![slice.T byteT] "enc".

Definition Unmarshal: val :=
  rec: "Unmarshal" "s" :=
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: "int" := ref (zero_val (struct.t completeint_gk.S)) in
    let: "slc" := ref (zero_val (struct.t completeslice_gk.S)) in
    let: "success" := ref (zero_val boolT) in
    let: "sslice" := ref (zero_val (slice.T (struct.t structslice_gk.S))) in
    let: "iints" := ref (zero_val (slice.T uint64T)) in
    let: ("0_ret", "1_ret") := completeint_gk.Unmarshal (![slice.T byteT] "enc") in
    "int" <-[struct.t completeint_gk.S] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := completeslice_gk.Unmarshal (![slice.T byteT] "enc") in
    "slc" <-[struct.t completeslice_gk.S] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadBool (![slice.T byteT] "enc") in
    "success" <-[boolT] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: "ssliceLen" := ref (zero_val uint64T) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "ssliceLen" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadSlice (struct.t structslice_gk.S) (![slice.T byteT] "enc") (![uint64T] "ssliceLen") structslice_gk.Unmarshal in
    "sslice" <-[slice.T (struct.t structslice_gk.S)] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: "iintsLen" := ref (zero_val uint64T) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "iintsLen" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadSlice uint64T (![slice.T byteT] "enc") (![uint64T] "iintsLen") marshal.ReadInt in
    "iints" <-[slice.T uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    (struct.mk S [
       "Int" ::= ![struct.t completeint_gk.S] "int";
       "Slc" ::= ![struct.t completeslice_gk.S] "slc";
       "Success" ::= ![boolT] "success";
       "Sslice" ::= ![slice.T (struct.t structslice_gk.S)] "sslice";
       "Iints" ::= ![slice.T uint64T] "iints"
     ], ![slice.T byteT] "enc").

End code.
