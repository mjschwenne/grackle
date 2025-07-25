(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.generatedproof.github_com.tchajed.marshal.
Require Export New.generatedproof.github_com.mjschwenne.grackle.testdata.out.go.completeint_gk.
Require Export New.generatedproof.github_com.mjschwenne.grackle.testdata.out.go.completeslice_gk.
Require Export New.generatedproof.github_com.mjschwenne.grackle.testdata.out.go.structslice_gk.
Require Export New.golang.theory.

Require Export New.code.github_com.mjschwenne.grackle.testdata.out.go.complete_gk.

Set Default Proof Using "Type".

Module complete_gk.

(* type complete_gk.S *)
Module S.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Int' : completeint_gk.S.t;
  Slc' : completeslice_gk.S.t;
  Success' : bool;
  Sslice' : slice.t;
  Iints' : slice.t;
  Sints' : slice.t;
}.
End def.
End S.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_S : Settable S.t :=
  settable! S.mk < S.Int'; S.Slc'; S.Success'; S.Sslice'; S.Iints'; S.Sints' >.
Global Instance into_val_S : IntoVal S.t :=
  {| to_val_def v :=
    struct.val_aux complete_gk.S [
    "Int" ::= #(S.Int' v);
    "Slc" ::= #(S.Slc' v);
    "Success" ::= #(S.Success' v);
    "Sslice" ::= #(S.Sslice' v);
    "Iints" ::= #(S.Iints' v);
    "Sints" ::= #(S.Sints' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_S : IntoValTyped S.t complete_gk.S :=
{|
  default_val := S.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_S_Int : IntoValStructField "Int" complete_gk.S S.Int'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_S_Slc : IntoValStructField "Slc" complete_gk.S S.Slc'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_S_Success : IntoValStructField "Success" complete_gk.S S.Success'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_S_Sslice : IntoValStructField "Sslice" complete_gk.S S.Sslice'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_S_Iints : IntoValStructField "Iints" complete_gk.S S.Iints'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_S_Sints : IntoValStructField "Sints" complete_gk.S S.Sints'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_S Int' Slc' Success' Sslice' Iints' Sints':
  PureWp True
    (struct.make #complete_gk.S (alist_val [
      "Int" ::= #Int';
      "Slc" ::= #Slc';
      "Success" ::= #Success';
      "Sslice" ::= #Sslice';
      "Iints" ::= #Iints';
      "Sints" ::= #Sints'
    ]))%struct
    #(S.mk Int' Slc' Success' Sslice' Iints' Sints').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance S_struct_fields_split dq l (v : S.t) :
  StructFieldsSplit dq l v (
    "HInt" ∷ l ↦s[complete_gk.S :: "Int"]{dq} v.(S.Int') ∗
    "HSlc" ∷ l ↦s[complete_gk.S :: "Slc"]{dq} v.(S.Slc') ∗
    "HSuccess" ∷ l ↦s[complete_gk.S :: "Success"]{dq} v.(S.Success') ∗
    "HSslice" ∷ l ↦s[complete_gk.S :: "Sslice"]{dq} v.(S.Sslice') ∗
    "HIints" ∷ l ↦s[complete_gk.S :: "Iints"]{dq} v.(S.Iints') ∗
    "HSints" ∷ l ↦s[complete_gk.S :: "Sints"]{dq} v.(S.Sints')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (S.Int' v)) complete_gk.S "Int"%go.
  simpl_one_flatten_struct (# (S.Slc' v)) complete_gk.S "Slc"%go.
  simpl_one_flatten_struct (# (S.Success' v)) complete_gk.S "Success"%go.
  simpl_one_flatten_struct (# (S.Sslice' v)) complete_gk.S "Sslice"%go.
  simpl_one_flatten_struct (# (S.Iints' v)) complete_gk.S "Iints"%go.

  solve_field_ref_f.
Qed.

End instances.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined complete_gk :=
{|
  is_pkg_defined := is_global_definitions complete_gk var_addrs;
|}.

Definition own_allocated : iProp Σ :=
True.

Global Instance wp_func_call_Marshal :
  WpFuncCall complete_gk "Marshal" _ (is_pkg_defined complete_gk) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Unmarshal :
  WpFuncCall complete_gk "Unmarshal" _ (is_pkg_defined complete_gk) :=
  ltac:(apply wp_func_call'; reflexivity).

End names.
End complete_gk.
