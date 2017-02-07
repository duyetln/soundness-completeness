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

(* TypeChecker proofs *)
Example tc_ex1 : typecheck (t_Num 1) [] = Some TNum.
Proof. reflexivity. Qed.

Example tc_ex2 : typecheck (t_Bool true) [] = Some TBool.
Proof. reflexivity. Qed.

Example tc_ex3 : typecheck (t_Cons (t_Num 2) (t_Nil TNum)) [] = Some (TList TNum).
Proof. reflexivity. Qed.

Example tc_ex4 : typecheck (t_Var "x") (("x", TNum)::[]) = Some TNum.
Proof. reflexivity. Qed.

Example tc_ex5 : typecheck (t_Fun "x" TNum (t_Binop op_Plus (t_Var "x") (t_Num 2))) [] = Some (TFun TNum TNum).
Proof. reflexivity. Qed.

Example tc_ex6 : typecheck (t_If (t_Binop op_Lt (t_Num 1) (t_Num 2)) (t_Bool true) (t_Bool false)) [] = Some TBool.
Proof. reflexivity. Qed.

Lemma tc_type_eqb_if : forall (t1 t2 : type),
  type_eqb t1 t2 = true ->
  t1 = t2.
Proof.
  intros t1 t2 H.
  induction t1; induction t2; try inversion H.
  - reflexivity.
  - reflexivity.
  - apply andb_true_iff in H1. 
    inversion H1.
Admitted.

Lemma tc_type_eqb_only_if : forall (t1 t2 : type),
  t1 = t2 ->
  type_eqb t1 t2 = true.
Proof.
  intros t1 t2 H.
  induction t1; induction t2; try inversion H.
  - reflexivity.
  - reflexivity.
  - simpl. apply andb_true_iff. split.
Admitted.

Theorem tc_t_Num : forall (n : nat) (e : environment), typecheck (t_Num n) e = Some TNum.
Proof. intros. reflexivity. Qed.

Theorem tc_t_Bool : forall (b : bool) (e : environment), typecheck (t_Bool b) e = Some TBool.
Proof. intros. reflexivity. Qed.

Theorem tc_t_If : forall (c e1 e2 : t_expr) (env : environment) (t1 t2 : type),
  typecheck c env = Some TBool ->
  typecheck e1 env = Some t1 -> 
  typecheck e2 env = Some t2 ->
  type_eqb t1 t2 = true ->
  typecheck (t_If c e1 e2) env = Some t1.
Proof.
  intros.
  simpl.
  rewrite H.
  rewrite H0.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Theorem tc_t_Fun : forall (x : string) (x_t e_t : type) (e : t_expr) (env : environment),
  typecheck e ((x, x_t)::env) = Some e_t ->
  typecheck (t_Fun x x_t e) env = Some (TFun x_t e_t).
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Theorem tc_t_Call : forall (f e : t_expr) (t1 t2 e_t : type) (env : environment),
  typecheck f env = Some (TFun t1 t2) ->
  typecheck e env = Some e_t ->
  type_eqb t1 e_t = true ->
  typecheck (t_Call f e) env = Some t2.
Proof.
  intros.
  simpl.
  rewrite H.
  rewrite H0.
  rewrite H1.
  reflexivity.
Qed.

Theorem tc_t_Binop_nnn : forall (e1 e2 : t_expr) (op : binop) (env : environment),
  typecheck e1 env = Some TNum ->
  typecheck e2 env = Some TNum ->
  op = op_Plus \/ op = op_Minus \/ op = op_Mult \/ op = op_Div \/ op = op_Mod ->
  typecheck (t_Binop op e1 e2) env = Some TNum.
Proof.
  intros.
  induction op; try (simpl; rewrite H; rewrite H0; reflexivity)
    ; try (intuition; discriminate).
Admitted.

Theorem tc_t_Nil : forall (t : type) (env : environment), typecheck (t_Nil t) env = Some (TList t).
Proof. reflexivity. Qed.
