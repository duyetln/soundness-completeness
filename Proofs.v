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

(* occurs *)
Lemma occurs_nontvar : forall i t, vartype t = false -> occurs i t = false.
Proof.
  intros i t H.
  induction t.
  - reflexivity.
  - reflexivity.
  - simpl. apply orb_false_iff. split.
    * inversion H. apply orb_false_iff in H1. destruct H1.
      rewrite H0. rewrite H1. simpl. apply IHt1. assumption.
    * inversion H. apply orb_false_iff in H1. destruct H1.
      rewrite H0. rewrite H1. simpl. apply IHt2. assumption.
  - simpl. inversion H. rewrite H1. apply IHt. assumption.
  - inversion H.
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
  apply SOL_NotEmpty.
  - reflexivity.
  - apply SOL_NotEmpty.
    * reflexivity.
    * apply SOL_NotEmpty.
      + reflexivity.
      + apply SOL_Empty.
Qed.

(* ################################################################# *)
(* Main goals *)
Theorem typeinference_soundness :
  forall (t : t_expr) (T : type)
    (e : ut_expr) (env : environment) (fv : nat) (S : type) (C : constraint),
  erase t e ->
  typecheck env t T ->
  typeinf env 0 e (fv, S, C) ->
  (exists s, unify ((S, T)::C) s).
Proof.
  intros t T e env fv S C He Htc Hti.
  destruct t.
  - inversion He. rewrite <- H1 in Hti.
    inversion Hti. inversion Htc.
    exists []. simpl. apply U_Identical with (t:=TNum).
    * apply U_Empty.
    * reflexivity.
    * reflexivity.
  - inversion He. rewrite <- H1 in Hti.
    inversion Hti. inversion Htc.
    exists []. simpl. apply U_Identical with (t:=TBool).
    * apply U_Empty.
    * reflexivity.
    * reflexivity.
  - inversion He. rewrite <- H1 in Hti.
    inversion Hti. inversion Htc.
    rewrite H10 in H5. inversion H5.
    exists []. simpl. apply U_Identical with (t:=S).
    * apply U_Empty.
    * reflexivity.
    * reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - inversion He. rewrite <- H1 in Hti.
    inversion Hti. inversion Htc.
    exists [(Id 0, t)].
    apply U_ListList with
      (tl_sub:=[])
      (list_sub:=[(Id 0, t)])
      (l1:=TVar (Id 0))
      (l2:=t).
    * apply U_Empty.
    * reflexivity.
    * reflexivity.
    * apply U_VarLeft.
      + apply U_Empty.
      + reflexivity.
      + reflexivity.
      + apply (occurs_nontvar (Id 0) t). assumption.
Admitted.
(*
Theorem typeinference_soundness :
  forall (t : t_expr) (T : type)
    (e : ut_expr) (env : environment) (fv : nat) (S : type) (C : constraint),
  erase t e ->
  typecheck env t T ->
  typeinf env 0 e (fv, S, C) ->
  (exists (s : substitution), solution s C /\ app_substs s S = T).
Proof.
  intros t T e env fv S C He Htc Hti.
  destruct t.
  - inversion He. rewrite <- H1 in Hti.
    inversion Hti. inversion Htc.
    exists []. simpl. split.
    * apply SOL_Empty.
    * reflexivity.
  - inversion He. rewrite <- H1 in Hti.
    inversion Hti. inversion Htc.
    exists []. simpl. split.
    * apply SOL_Empty.
    * reflexivity.
  - inversion He. rewrite <- H1 in Hti.
    inversion Hti. inversion Htc.
    rewrite H10 in H5. inversion H5.
    exists []. simpl. split.
    * apply SOL_Empty.
    * reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - inversion He. rewrite <- H2 in Hti.
    inversion Hti. inversion Htc.
  - inversion He. rewrite <- H1 in Hti.
    inversion Hti. inversion Htc.
    exists [(Id 0, t)]. split.
    * apply SOL_Empty.
    * reflexivity.
Admitted.
*)

Theorem typeinference_completeness :
  forall (e : ut_expr) (env : environment) (fv : nat) (S : type) (C :constraint) (s : substitution),
  typeinf env 0 e (fv, S, C) ->
  solution s C ->
  (exists (t : t_expr), erase t e /\ typecheck env t (app_substs s S)).
Proof.
  intros e env fv S C s Hti Hs.
  induction e.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
