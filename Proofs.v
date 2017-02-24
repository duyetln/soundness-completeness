Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import Maps.
Require Import LibTactics.
Require Import AST.
Require Import TypeInferencer.
Require Import TypeChecker.

(* ################################################################# *)
(* Small proofs *)

(* occurs *)
Lemma occurs_nontvar : forall i t, vartype t = false -> occurs i t = false.
Proof.
  introv H.
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

(* subst *)
Lemma subst_vartype_false : forall i t t', vartype t = false  -> subst (i, t') t = t.
Proof.
  introv Hvt.
  induction t.
  - reflexivity.
  - reflexivity.
  - inversion Hvt. apply orb_false_iff in H0. destruct H0.
    intuition. simpl. rewrite H1, H2. reflexivity.
  - inversion Hvt. intuition. simpl. rewrite H. reflexivity.
  - inversion Hvt.
Qed.

(* app_substs *)
Lemma app_substs_nontvar : forall s t, vartype t = false -> app_substs s t = t.
Proof.
  introv H.
  induction s as [|hd tl].
  - reflexivity.
  - destruct t.
    * simpl. rewrite IHtl. destruct hd. apply subst_vartype_false. assumption.
    * simpl. rewrite IHtl. destruct hd. apply subst_vartype_false. assumption.
    * simpl. rewrite IHtl. destruct hd. apply subst_vartype_false. assumption.
    * simpl. rewrite IHtl. destruct hd. apply subst_vartype_false. assumption.
    * inversion H.
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
(*
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
  - inverts He. inverts Hti. inverts Htc.
    exists (@nil (id * type) % type). simpl. apply U_Identical with (t:=TNum).
    * apply U_Empty.
    * reflexivity.
    * reflexivity.
  - inverts He. inverts Hti. inverts Htc.
    exists (@nil (id * type) % type). simpl. apply U_Identical with (t:=TBool).
    * apply U_Empty.
    * reflexivity.
    * reflexivity.
  - inverts He. inverts Hti. inverts Htc.
    rewrite H1 in H3. inverts H3.
    exists (@nil (id * type) % type). simpl. apply U_Identical with (t:=S).
    * apply U_Empty.
    * reflexivity.
    * reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
(*
| U_ListList:
    forall t1 t2 tl tl_sub
      l1 l2 list_sub,
    unify tl tl_sub ->
    app_substs tl_sub t1 = TList l1 ->
    app_substs tl_sub t2 = TList l2 ->
    unify [(l1, l2)] list_sub ->
    unify ((t1, t2)::tl) (list_sub ++ tl_sub)
*)
(*
unify ((TList hd_T, TList T0) :: tl_C ++ hd_C ++ [(tl_T, TList hd_T)]) ?s
*)
  - inverts He. inverts Hti. inverts Htc. sort.
    eexists.
    apply U_ListList with
  - inverts He. inverts Hti. inverts Htc.
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
*)
Theorem typeinference_soundness :
  forall (t : t_expr) (T : type)
    (e : ut_expr) (env : environment) (fv : nat) (S : type) (C : constraint),
  erase t e ->
  typecheck env t T ->
  typeinf env 0 e (fv, S, C) ->
  (exists (s : substitution), solution s C /\ app_substs s S = T).
Proof.
  introv He Htc Hti.
  destruct t.
  - inverts He. inverts Hti. inverts Htc.
    exists (@nil (id * type) % type). simpl. split.
    * apply SOL_Empty.
    * reflexivity.
  - inverts He. inverts Hti. inverts Htc.
    exists (@nil (id * type) % type). simpl. split.
    * apply SOL_Empty.
    * reflexivity.
  - inverts He. inverts Hti. inverts Htc.
    rewrite H0 in H3. inverts H3.
    exists (@nil (id * type) % type). simpl. split.
    * apply SOL_Empty.
    * reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - inverts He. inverts Hti. inverts Htc.
    exists [(Id 0, t)]. split.
    * apply SOL_Empty.
    * reflexivity.
Admitted.

Theorem typeinference_completeness :
  forall (e : ut_expr) (T : type) (env : environment) (fv : nat) (S : type) (C :constraint),
  typeinf env 0 e (fv, S, C) ->
  (exists (s : substitution),
    solution s C /\
    app_substs s S = T /\
    vartype T = false) ->
  (exists (t : t_expr), erase t e /\ typecheck env t T).
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
