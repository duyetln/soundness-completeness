Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.
Require Import TypeInferencer.
Require Import TypeChecker.

(* Main goals *)
Theorem typeinference_soundness :
  forall (t : t_expr) (T : type)
    (e : ut_expr) (env : environment) (fv : nat) (S : type) (C : constraint),
  env = (@empty type) ->
  erase t = e ->
  typecheck env t T ->
  typeinf env 0 e (fv, S, C) ->
  (exists (s : substitution), solution s C /\ apply s S = T).
Proof.
Admitted.

Theorem typeinference_completeness :
  forall (e : ut_expr) (env : environment) (fv : nat) (S : type) (C :constraint) (s : substitution),
  env = (@empty type) ->
  typeinf env 0 e (fv, S, C) ->
  solution s C ->
  (exists (t : t_expr), erase t = e /\ typecheck env t (apply s S)).
Proof.
Admitted.