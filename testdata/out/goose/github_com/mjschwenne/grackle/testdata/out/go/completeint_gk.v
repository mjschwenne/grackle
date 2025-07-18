(* autogenerated from github.com/mjschwenne/grackle/testdata/out/go/completeint_gk *)
From New.golang Require Import defn.
Require Export New.code.github_com.tchajed.marshal.

Definition completeint_gk : go_string := "github.com/mjschwenne/grackle/testdata/out/go/completeint_gk".

Module completeint_gk.
Section code.
Context `{ffi_syntax}.


Definition S : go_type := structT [
  "One" :: uint32T;
  "Two" :: uint32T;
  "Three" :: uint32T;
  "Four" :: uint64T;
  "Five" :: uint64T;
  "Six" :: uint64T
].

(* go: completeint_gk.go:21:6 *)
Definition Marshal : val :=
  rec: "Marshal" "enc" "c" :=
    exception_do (let: "c" := (mem.alloc "c") in
    let: "enc" := (mem.alloc "enc") in
    let: "$r0" := (let: "$a0" := (![#sliceT] "enc") in
    let: "$a1" := (![#uint32T] (struct.field_ref #S #"One"%go "c")) in
    (func_call #marshal.marshal #"WriteInt32"%go) "$a0" "$a1") in
    do:  ("enc" <-[#sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "enc") in
    let: "$a1" := (![#uint32T] (struct.field_ref #S #"Two"%go "c")) in
    (func_call #marshal.marshal #"WriteInt32"%go) "$a0" "$a1") in
    do:  ("enc" <-[#sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "enc") in
    let: "$a1" := (![#uint32T] (struct.field_ref #S #"Three"%go "c")) in
    (func_call #marshal.marshal #"WriteInt32"%go) "$a0" "$a1") in
    do:  ("enc" <-[#sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "enc") in
    let: "$a1" := (![#uint64T] (struct.field_ref #S #"Four"%go "c")) in
    (func_call #marshal.marshal #"WriteInt"%go) "$a0" "$a1") in
    do:  ("enc" <-[#sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "enc") in
    let: "$a1" := (![#uint64T] (struct.field_ref #S #"Five"%go "c")) in
    (func_call #marshal.marshal #"WriteInt"%go) "$a0" "$a1") in
    do:  ("enc" <-[#sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "enc") in
    let: "$a1" := (![#uint64T] (struct.field_ref #S #"Six"%go "c")) in
    (func_call #marshal.marshal #"WriteInt"%go) "$a0" "$a1") in
    do:  ("enc" <-[#sliceT] "$r0");;;
    return: (![#sliceT] "enc")).

(* go: completeint_gk.go:32:6 *)
Definition Unmarshal : val :=
  rec: "Unmarshal" "s" :=
    exception_do (let: "s" := (mem.alloc "s") in
    let: "one" := (mem.alloc (type.zero_val #uint32T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![#sliceT] "s") in
    (func_call #marshal.marshal #"ReadInt32"%go) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("one" <-[#uint32T] "$r0");;;
    do:  ("s" <-[#sliceT] "$r1");;;
    let: "two" := (mem.alloc (type.zero_val #uint32T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![#sliceT] "s") in
    (func_call #marshal.marshal #"ReadInt32"%go) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("two" <-[#uint32T] "$r0");;;
    do:  ("s" <-[#sliceT] "$r1");;;
    let: "three" := (mem.alloc (type.zero_val #uint32T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![#sliceT] "s") in
    (func_call #marshal.marshal #"ReadInt32"%go) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("three" <-[#uint32T] "$r0");;;
    do:  ("s" <-[#sliceT] "$r1");;;
    let: "four" := (mem.alloc (type.zero_val #uint64T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![#sliceT] "s") in
    (func_call #marshal.marshal #"ReadInt"%go) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("four" <-[#uint64T] "$r0");;;
    do:  ("s" <-[#sliceT] "$r1");;;
    let: "five" := (mem.alloc (type.zero_val #uint64T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![#sliceT] "s") in
    (func_call #marshal.marshal #"ReadInt"%go) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("five" <-[#uint64T] "$r0");;;
    do:  ("s" <-[#sliceT] "$r1");;;
    let: "six" := (mem.alloc (type.zero_val #uint64T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![#sliceT] "s") in
    (func_call #marshal.marshal #"ReadInt"%go) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("six" <-[#uint64T] "$r0");;;
    do:  ("s" <-[#sliceT] "$r1");;;
    return: (let: "$One" := (![#uint32T] "one") in
     let: "$Two" := (![#uint32T] "two") in
     let: "$Three" := (![#uint32T] "three") in
     let: "$Four" := (![#uint64T] "four") in
     let: "$Five" := (![#uint64T] "five") in
     let: "$Six" := (![#uint64T] "six") in
     struct.make #S [{
       "One" ::= "$One";
       "Two" ::= "$Two";
       "Three" ::= "$Three";
       "Four" ::= "$Four";
       "Five" ::= "$Five";
       "Six" ::= "$Six"
     }], ![#sliceT] "s")).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("Marshal"%go, Marshal); ("Unmarshal"%go, Unmarshal)].

Definition msets' : list (go_string * (list (go_string * val))) := [("S"%go, []); ("S'ptr"%go, [])].

#[global] Instance info' : PkgInfo completeint_gk.completeint_gk :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [marshal.marshal];
  |}.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init completeint_gk.completeint_gk (λ: <>,
      exception_do (do:  marshal.initialize')
      ).

End code.
End completeint_gk.
