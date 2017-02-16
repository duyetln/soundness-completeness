Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import TypeInferencer.
Require Import TypeChecker.

Theorem typeinference_soundness :
  forall (t : t_expr) (T : type)
    (e : ut_expr) (S : type) (C : constraint),
  erase t = e ->
  typecheck t T ->
  typeinf e (S, C) ->
  (exists (s : substitution), solution s C /\ apply s S = T).
Proof.
Admitted.

Theorem typeinference_completeness :
  forall (e : ut_expr) (S : type) (C :constraint) (s : substitution),
  typeinf e (S, C) ->
  solution s C ->
  (exists (t : t_expr), erase t = e /\ typecheck t (apply s S)).
Proof.
Admitted.