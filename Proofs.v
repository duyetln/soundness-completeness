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

(* ################################################################# *)
(* Small proofs *)

(* erase *)
Lemma erase_num : forall n ut, erase (t_Num n) = ut <-> ut = ut_Num n.
Proof.
  intros. simpl.
  split; try (intros; symmetry; assumption).
Qed.

Lemma erase_bool : forall b ut, erase (t_Bool b)= ut <-> ut = ut_Bool b.
Proof.
  intros. simpl.
  split; try (intros; symmetry; assumption).
Qed.

Lemma erase_var : forall x ut, erase (t_Var x) = ut <-> ut = ut_Var x.
Proof.
  intros. simpl.
  split; try (intros; symmetry; assumption).
Qed.

Lemma erase_if : forall c_t c_ut e1_t e1_ut e2_t e2_ut ut,
  erase c_t = c_ut ->
  erase e1_t = e1_ut ->
  erase e2_t = e2_ut ->
  (erase (t_If c_t e1_t e2_t) = ut <-> ut = ut_If c_ut e1_ut e2_ut).
Proof.
  intros. simpl.
  rewrite H. rewrite H0. rewrite H1.
  split; try (intros; symmetry; assumption).
Qed.

Lemma erase_fun : forall x T e_t e_ut ut,
  erase e_t = e_ut ->
  (erase (t_Fun x T e_t) = ut <-> ut = ut_Fun x e_ut).
Proof.
  intros. simpl.
  rewrite H.
  split; try (intros; symmetry; assumption).
Qed.

Lemma erase_call : forall f_t f_ut e_t e_ut ut,
  erase f_t = f_ut ->
  erase e_t = e_ut ->
  (erase (t_Call f_t e_t) = ut <-> ut = ut_Call f_ut e_ut).
Proof.
  intros. simpl.
  rewrite H. rewrite H0.
  split; try (intros; symmetry; assumption).
Qed.

Lemma erase_binop : forall op e1_t e1_ut e2_t e2_ut ut,
  erase e1_t = e1_ut ->
  erase e2_t = e2_ut ->
  (erase (t_Binop op e1_t e2_t) = ut <-> ut = ut_Binop op e1_ut e2_ut).
Proof.
  intros. simpl.
  rewrite H. rewrite H0.
  split; try (intros; symmetry; assumption).
Qed.

Lemma erase_cons : forall hd_t hd_ut tl_t tl_ut ut,
  erase hd_t = hd_ut ->
  erase tl_t = tl_ut ->
  (erase (t_Cons hd_t tl_t) = ut <-> ut = ut_Cons hd_ut tl_ut).
Proof.
  intros. simpl.
  rewrite H. rewrite H0.
  split; try (intros; symmetry; assumption).
Qed.

Lemma erase_nil : forall T ut,
  erase (t_Nil T) = ut <-> ut = ut_Nil.
Proof.
  intros. simpl.
  split; try (intros; symmetry; assumption).
Qed.

(* app_substs *)
Example app_substs_ex1 : app_substs [(Id 1, TNum)] (TFun (TVar (Id 1)) TNum) = TFun TNum TNum.
Proof. reflexivity. Qed.

Example app_substs_ex2 : app_substs [(Id 1, TNum);(Id 2, TBool)] (TFun (TVar (Id 1)) (TVar (Id 2))) = TFun TNum TBool.
Proof. reflexivity. Qed.

(* solution *)
Example solution_ex1 :
  solution
    [(Id 1, TNum); (Id 2, TNum); (Id 3, TNum)]
    [(TList (TVar (Id 1)), TList TNum); (TList (TVar (Id 3)), TList TNum); (TVar (Id 2), TNum)].
Proof.
  apply S_NotEmpty.
  - reflexivity.
  - apply S_NotEmpty.
    * reflexivity.
    * apply S_NotEmpty.
      + reflexivity.
      + apply S_Empty.
Qed.

(* ################################################################# *)
(* Main goals *)
Theorem typeinference_soundness :
  forall (t : t_expr) (T : type)
    (e : ut_expr) (env : environment) (fv : nat) (S : type) (C : constraint),
  erase t = e ->
  typecheck env t T ->
  typeinf env 0 e (fv, S, C) ->
  (exists (s : substitution), solution s C /\ app_substs s S = T).
Proof.
  intros t T e env fv S C He Htc Hti.
  induction t.
  - apply erase_num in He. rewrite He in Hti.
    inversion Hti. inversion Htc.
    exists []. simpl. split.
    * apply S_Empty.
    * reflexivity.
  - apply erase_bool in He. rewrite He in Hti.
    inversion Hti. inversion Htc.
    exists []. simpl. split.
    * apply S_Empty.
    * reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Theorem typeinference_completeness :
  forall (e : ut_expr) (env : environment) (fv : nat) (S : type) (C :constraint) (s : substitution),
  typeinf env 0 e (fv, S, C) ->
  solution s C ->
  (exists (t : t_expr), erase t = e /\ typecheck env t (app_substs s S)).
Proof.
Admitted.