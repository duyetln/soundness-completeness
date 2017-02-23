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
Lemma erase_common : forall t ut1 ut2,
  erase t ut1 ->
  erase t ut2 ->
  ut1 = ut2.
Proof.
Admitted.


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
