(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.generatedproof.github_com.goose_lang.primitive.
Require Export New.generatedproof.github_com.goose_lang.std.
Require Export New.generatedproof.github_com.tchajed.marshal.
Require Export New.generatedproof.github_com.mjschwenne.grackle.testdata.out.go.timestamp_gk.
Require Export New.golang.theory.

Require Export New.code.github_com.mjschwenne.grackle.testdata.out.go.event_gk.

Set Default Proof Using "Type".

Module event_gk.

(* type event_gk.S *)
Module S.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Id' : w32;
  Name' : go_string;
  StartTime' : timestamp_gk.S.t;
  EndTime' : timestamp_gk.S.t;
}.
End def.
End S.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_S : Settable S.t :=
  settable! S.mk < S.Id'; S.Name'; S.StartTime'; S.EndTime' >.
Global Instance into_val_S : IntoVal S.t :=
  {| to_val_def v :=
    struct.val_aux event_gk.S [
    "Id" ::= #(S.Id' v);
    "Name" ::= #(S.Name' v);
    "StartTime" ::= #(S.StartTime' v);
    "EndTime" ::= #(S.EndTime' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_S : IntoValTyped S.t event_gk.S :=
{|
  default_val := S.mk (default_val _) (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_S_Id : IntoValStructField "Id" event_gk.S S.Id'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_S_Name : IntoValStructField "Name" event_gk.S S.Name'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_S_StartTime : IntoValStructField "StartTime" event_gk.S S.StartTime'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_S_EndTime : IntoValStructField "EndTime" event_gk.S S.EndTime'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_S Id' Name' StartTime' EndTime':
  PureWp True
    (struct.make #event_gk.S (alist_val [
      "Id" ::= #Id';
      "Name" ::= #Name';
      "StartTime" ::= #StartTime';
      "EndTime" ::= #EndTime'
    ]))%struct
    #(S.mk Id' Name' StartTime' EndTime').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance S_struct_fields_split dq l (v : S.t) :
  StructFieldsSplit dq l v (
    "HId" ∷ l ↦s[event_gk.S :: "Id"]{dq} v.(S.Id') ∗
    "HName" ∷ l ↦s[event_gk.S :: "Name"]{dq} v.(S.Name') ∗
    "HStartTime" ∷ l ↦s[event_gk.S :: "StartTime"]{dq} v.(S.StartTime') ∗
    "HEndTime" ∷ l ↦s[event_gk.S :: "EndTime"]{dq} v.(S.EndTime')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (S.Id' v)) event_gk.S "Id"%go.
  simpl_one_flatten_struct (# (S.Name' v)) event_gk.S "Name"%go.
  simpl_one_flatten_struct (# (S.StartTime' v)) event_gk.S "StartTime"%go.

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

Global Instance is_pkg_defined_instance : IsPkgDefined event_gk :=
{|
  is_pkg_defined := is_global_definitions event_gk var_addrs;
|}.

Definition own_allocated : iProp Σ :=
True.

Global Instance wp_func_call_Marshal :
  WpFuncCall event_gk "Marshal" _ (is_pkg_defined event_gk) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Unmarshal :
  WpFuncCall event_gk "Unmarshal" _ (is_pkg_defined event_gk) :=
  ltac:(apply wp_func_call'; reflexivity).

End names.
End event_gk.
