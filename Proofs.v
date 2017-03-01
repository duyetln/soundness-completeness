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

(* app_substs *)
Example app_substs_ex1 : app_substs [(Id 1, inft_Num)] (inft_Fun (inft_Var (Id 1)) inft_Num) = inft_Fun inft_Num inft_Num.
Proof. reflexivity. Qed.

Example app_substs_ex2 : app_substs [(Id 1, inft_Num);(Id 2, inft_Bool)] (inft_Fun (inft_Var (Id 1)) (inft_Var (Id 2))) = inft_Fun inft_Num inft_Bool.
Proof. reflexivity. Qed.

(* solution *)
Example solution_ex1 :
  solution
    [(Id 1, inft_Num); (Id 2, inft_Num); (Id 3, inft_Num)]
    [(inft_List (inft_Var (Id 1)), inft_List inft_Num); (inft_List (inft_Var (Id 3)), inft_List inft_Num); (inft_Var (Id 2), inft_Num)].
Proof.
  apply SOL_NotEmpty.
  - reflexivity.
  - apply SOL_NotEmpty.
    * reflexivity.
    * apply SOL_NotEmpty.
      + reflexivity.
      + apply SOL_Empty.
Qed.

(* convert_type *)
Lemma exists_inf_type_to_cont_type :
  forall ct, exists it, convert_type it ct.
Proof.
  introv.
  induction ct.
  - exists inft_Num. apply CT_Num.
  - exists inft_Bool. apply CT_Bool.
  - destruct IHct1 as [it1 IHt1]. destruct IHct2 as [it2 IHt2].
    exists (inft_Fun it1 it2). apply CT_Fun.
    * assumption.
    * assumption.
  - destruct IHct as [it' IHt].
    exists (inft_List it'). apply CT_List. assumption.
Qed.

(* convert_expr *)
Lemma exists_type_for_nil :
  forall t, convert_expr t ut_Nil -> exists t', t = t_Nil t'.
Proof.
  introv H. inverts H. exists t0. reflexivity.
Qed.

(* substs *)
Lemma subst_nontvar : 
  forall s TI, (exists TC, convert_type TI TC) -> subst s TI = TI.
Proof.
  introv Hvt.
  induction TI.
  - reflexivity.
  - reflexivity.
  - inverts Hvt. inverts H. simpl.
    assert (Htc1: exists tc, convert_type TI1 tc). { exists x_t. assumption. }
    assert (Htc2: exists tc, convert_type TI2 tc). { exists e_t. assumption. }
    apply IHTI1 in Htc1.
    apply IHTI2 in Htc2.
    rewrite Htc1, Htc2.
    reflexivity.
  - inverts Hvt. inverts H. simpl.
    assert (Htc: exists tc, convert_type TI tc). { exists l_t. assumption. }
    apply IHTI in Htc.
    rewrite Htc.
    reflexivity.
  - inverts Hvt. inverts H.
Qed.

Lemma subst_form_any :
  forall s t, exists t', subst s t = t'.
Proof.
  introv.
  induction t.
  - exists inft_Num. reflexivity.
  - exists inft_Bool. reflexivity.
  - destruct IHt1 as [t1' H1]. destruct IHt2 as [t2' H2].
    exists (inft_Fun t1' t2'). simpl.
    rewrite H1, H2. reflexivity.
  - destruct IHt as [t'' H].
    exists (inft_List t''). simpl.
    rewrite H. reflexivity.
  - destruct s as [x y]. simpl. destruct beq_id.
    * exists y. reflexivity.
    * exists (inft_Var i). reflexivity.
Qed.

Lemma subst_form_num :
  forall s, subst s inft_Num = inft_Num.
Proof. reflexivity. Qed.

Lemma subst_form_bool :
  forall s, subst s inft_Bool = inft_Bool.
Proof. reflexivity. Qed.

Lemma subst_form_list :
  forall s t, exists t', subst s (inft_List t) = inft_List t'.
Proof.
  introv.
  simpl.
  assert (H: exists t'', subst s t = t'').
    { apply subst_form_any. }
  destruct H as [t'' H]. exists t''. rewrite H. reflexivity.
Qed.

Lemma subst_form_fun :
  forall s t1 t2, exists t1' t2', subst s (inft_Fun t1 t2) = inft_Fun t1' t2'.
Proof.
  introv.
  simpl.
  assert (H1: exists t1'', subst s t1 = t1'').
    { apply subst_form_any. }
  assert (H2: exists t2'', subst s t2 = t2'').
    { apply subst_form_any. }
  destruct H1 as [t1'' H1]. destruct H2 as [t2'' H2].
  rewrite H1, H2.
  exists t1'' t2''.
  reflexivity.
Qed.

(* app_substs *)
Lemma app_substs_nontvar :
  forall TI s, (exists TC, convert_type TI TC) -> app_substs s TI = TI.
Proof.
  introv H.
  induction s as [|hd tl].
  - reflexivity.
  - destruct TI.
    * simpl. rewrite IHtl. apply subst_nontvar. assumption.
    * simpl. rewrite IHtl. apply subst_nontvar. assumption.
    * simpl. rewrite IHtl. apply subst_nontvar. assumption.
    * simpl. rewrite IHtl. apply subst_nontvar. assumption.
    * inverts H. inverts H0.
Qed.

Lemma app_substs_form_num :
  forall s, app_substs s inft_Num = inft_Num.
Proof.
  introv.
  assert (H: exists t, convert_type inft_Num t).
    { exists cont_Num. apply CT_Num. }
  apply (app_substs_nontvar inft_Num s). assumption.
Qed.

Lemma app_substs_form_bool :
  forall s, app_substs s inft_Bool = inft_Bool.
Proof.
  introv.
  assert (H: exists t, convert_type inft_Bool t).
    { exists cont_Bool. apply CT_Bool. }
  apply (app_substs_nontvar inft_Bool s). assumption.
Qed.

Lemma app_substs_form_list :
  forall s t, exists t', app_substs s (inft_List t) = inft_List t'.
Proof.
  introv.
  induction s as [|hd tl].
  - exists t. reflexivity.
  - simpl. destruct IHtl as [t'' Htl].
    rewrite Htl. apply (subst_form_list hd t'').
Qed.
Qed.

(* ################################################################# *)
(* Main goals *)

Theorem typeinference_soundness :
  forall
    t T tc_env
    e S ti_env
    C fv,
  convert_expr t e ->
  typecheck tc_env t T ->
  typeinf ti_env 0 e (fv, S, C) ->
  (forall i TC TI, tc_env i = Some TC /\ ti_env i = Some TI -> (exists s', convert_type (app_substs s' TI) TC)) ->
  (exists s, solution s C /\ convert_type (app_substs s S) T).
Proof.
  introv Hc Htc Hti Hvar.
  destruct t.
  - inverts Hc. inverts Hti. inverts Htc.
    exists (@nil (id * inft_type) % type). simpl. split.
    * apply SOL_Empty.
    * apply CT_Num.
  - inverts Hc. inverts Hti. inverts Htc.
    exists (@nil (id * inft_type) % type). simpl. split.
    * apply SOL_Empty.
    * apply CT_Bool.
  - inverts Hc. inverts Hti. inverts Htc.
    assert (Hconv: exists s', convert_type (app_substs s' S) T).
        { apply (Hvar i T S). split. assumption. assumption. }
    destruct Hconv as [s' Hconv].
    exists s'. split.
    * apply SOL_Empty.
    * assumption.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - inverts Hc. inverts Hti. inverts Htc.
    assert (HS': exists S', convert_type S' c).
      { apply exists_inf_type_to_cont_type. }
    destruct HS' as [S' HS'].
    exists [(Id 0, S')]. simpl. split.
    * apply SOL_Empty.
    * apply CT_List. assumption.
Admitted.

Theorem typeinference_completeness :
  forall
    (ti_env : ti_env) e fv S C T,
  typeinf ti_env 0 e (fv, S, C) ->
  (exists s, solution s C /\ convert_type (app_substs s S) T) ->
  (exists t tc_env, convert_expr t e /\ typecheck tc_env t T).
Proof.
  introv Hti Hsub.
  destruct Hsub as [sub [Hsubsol Hsubconv]]. sort.
  induction e.
  - exists (t_Num n) (@empty cont_type). split.
    * apply CE_Num.
    * inverts Hti.
      assert (Htnum: exists tc, convert_type inft_Num tc).
        { exists cont_Num. apply CT_Num. }
      apply (app_substs_nontvar inft_Num sub) in Htnum.
      rewrite Htnum in Hsubconv. inverts Hsubconv. apply TC_Num.
  - exists (t_Bool b) (@empty cont_type). split.
    * apply CE_Bool.
    * inverts Hti.
      assert (Htbool: exists tc, convert_type inft_Bool tc).
        { exists cont_Bool. apply CT_Bool. }
      apply (app_substs_nontvar inft_Bool sub) in Htbool.
      rewrite Htbool in Hsubconv. inverts Hsubconv. apply TC_Bool.
  - exists (t_Var i) (update (@empty cont_type) i T). split.
    * apply CE_Var.
    * apply TC_Var. apply update_eq.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - inverts Hti.
    assert (Hflist: exists t', app_substs sub (inft_List (inft_Var (Id 0))) = inft_List t').
      { apply (app_substs_form_list sub (inft_Var (Id 0))). }
    inverts Hflist. rewrite H in Hsubconv.
    inverts Hsubconv.
    exists (t_Nil l_t) (@empty cont_type). split.
    * apply CE_Nil.
    * apply TC_Nil.
Admitted.
