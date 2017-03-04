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

Lemma solution_constr_concat :
  forall s C1 C2, solution s C1 /\ solution s C2 <-> solution s (C1 ++ C2).
Proof.
  introv. split.
  - introv [HC1 HC2]. induction C1 as [|hd1 tl1].
    * simpl. assumption.
    * simpl. inverts HC1.
      apply SOL_NotEmpty.
      + assumption.
      + apply (IHtl1 H3).
  - introv H. induction C1 as [|hd1 tl1]; simpl in H.
    * split.
      + apply SOL_Empty.
      + assumption.
    * inverts H. apply IHtl1 in H4. inverts H4. split.
      + apply SOL_NotEmpty.
        { assumption. }
        { assumption. }
      + assumption.
Qed.

(* convert_type *)
Lemma exists_inft_type_to_cont_type :
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

Lemma app_substs_sub_list :
  forall s t, app_substs s (inft_List t) = inft_List (app_substs s t).
Proof.
  introv.
  induction s as [|hd tl].
  - reflexivity.
  - simpl. rewrite IHtl. simpl. reflexivity.
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
(*
Proof.
  introv.
  rewrite (app_substs_sub_list s t).
  exists (app_substs s t). reflexivity.
Qed.
*)

Lemma app_substs_sub_fun :
  forall s t1 t2, app_substs s (inft_Fun t1 t2) = inft_Fun (app_substs s t1) (app_substs s t2).
Proof.
  introv.
  induction s as [|hd tl].
  - reflexivity.
  - simpl. rewrite IHtl. simpl. reflexivity.
Qed.

Lemma app_substs_form_fun :
  forall s t1 t2, exists t1' t2', app_substs s (inft_Fun t1 t2) = inft_Fun t1' t2'.
Proof.
  introv.
  induction s as [|hd tl].
  - exists t1 t2. reflexivity.
  - simpl. destruct IHtl as [t1'' [t2'' Htl]].
    rewrite Htl. apply (subst_form_fun hd t1'' t2'').
Qed.
(*
Proof.
  introv.
  rewrite (app_substs_sub_fun s t1 t2).
  exists (app_substs s t1) (app_substs s t2). reflexivity.
Qed.
*)


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
        { apply (Hvar i T S). split; assumption. }
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
      { apply exists_inft_type_to_cont_type. }
    destruct HS' as [S' HS'].
    exists [(Id 0, S')]. simpl. split.
    * apply SOL_Empty.
    * apply CT_List. assumption.
Admitted.

Theorem typeinference_completeness :
  forall
    (ti_env : ti_env) (tc_env : tc_env) e fv1 fv2 S C T,
  typeinf ti_env fv1 e (fv2, S, C) ->
  (exists s, solution s C /\ convert_type (app_substs s S) T) ->
  (forall i TI TC, ti_env i = Some TI /\ (exists s', convert_type (app_substs s' TI) TC) -> tc_env i = Some TC) ->
  (exists t, convert_expr t e /\ typecheck tc_env t T).
Proof.
  induction e;
  introv Hti Hsub Henv;
  destruct Hsub as [sub [Hsubsol Hsubconv]];
  inverts Hti as Htie1 Htie2 Htie3; sort.
  (* ut_Num *)
  - exists (t_Num n). split.
    * apply CE_Num.
    * rewrite app_substs_form_num in Hsubconv.
      inverts Hsubconv. apply TC_Num.
  (* ut_Bool *)
  - exists (t_Bool b). split.
    * apply CE_Bool.
    * rewrite app_substs_form_bool in Hsubconv.
      inverts Hsubconv. apply TC_Bool.
  (* ut_Var *)
  - exists (t_Var i). split.
    * apply CE_Var.
    * apply TC_Var. apply (Henv i S T). split.
      + assumption.
      + exists sub. assumption.
  (* ut_If *)
  - (* solution sub c_C *)
    assert (Hsol_c_C: solution sub c_C).
      { apply (solution_constr_concat sub c_C [(S, e2_T); (c_T, inft_Bool)]).
        apply (solution_constr_concat sub e1_C (c_C ++ [(S, e2_T); (c_T, inft_Bool)])).
        apply (solution_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, inft_Bool)])).
        assumption. }
    (* solution sub e1_C *)
    assert (Hsol_e1_C: solution sub e1_C).
      { apply (solution_constr_concat sub e1_C (c_C ++ [(S, e2_T); (c_T, inft_Bool)])).
        apply (solution_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, inft_Bool)])).
        assumption. }
    (* solution sub e2_C *)
    assert (Hsol_e2_C: solution sub e2_C).
      { apply (solution_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, inft_Bool)])).
        assumption. }
    (* convert_type (app_substs sub c_T) cont_Bool *)
    assert (Hsol_c_T: solution sub [(c_T, inft_Bool)]).
      { apply (solution_constr_concat sub [(S, e2_T)] [(c_T, inft_Bool)]).
        apply (solution_constr_concat sub c_C [(S, e2_T); (c_T, inft_Bool)]).
        apply (solution_constr_concat sub e1_C (c_C ++ [(S, e2_T); (c_T, inft_Bool)])).
        apply (solution_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, inft_Bool)])).
        assumption. }
    inverts Hsol_c_T as Hc_bool.
    assert (Hsubsts_c_T: convert_type (app_substs sub c_T) cont_Bool).
      { rewrite Hc_bool, (app_substs_form_bool sub). apply CT_Bool. }
    (* convert_type (app_substs sub S) T *)
    assert (Hsubsts_S: convert_type (app_substs sub S) T).
      { assumption. }
    (* convert_type (app_substs sub e2_T) T *)
    assert (Hsol_e2_T: solution sub [(S, e2_T)]).
      { apply (solution_constr_concat sub [(S, e2_T)] [(c_T, inft_Bool)]).
        apply (solution_constr_concat sub c_C [(S, e2_T); (c_T, inft_Bool)]).
        apply (solution_constr_concat sub e1_C (c_C ++ [(S, e2_T); (c_T, inft_Bool)])).
        apply (solution_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, inft_Bool)])).
        assumption. }
    inverts Hsol_e2_T as HS_e2_T.
    assert (Hsubsts_e2_T: convert_type (app_substs sub e2_T) T).
      { rewrite <- HS_e2_T. assumption. }
    (* exists s, solution s c_C /\ convert_type (app_substs s c_T) cont_Bool *)
    assert (Hsubc: exists s, solution s c_C /\ convert_type (app_substs s c_T) cont_Bool).
      { exists sub. split; assumption. }
    (* exists s, solution s e1_C /\ convert_type (app_substs s S) T *)
    assert (Hsube1: exists s, solution s e1_C /\ convert_type (app_substs s S) T).
      { exists sub. split; assumption. }
    (* exists s, solution s e2_C /\ convert_type (app_substs s e2_T) T *)
    assert (Hsube2: exists s, solution s e2_C /\ convert_type (app_substs s e2_T) T).
      { exists sub. split; assumption. }
    (* exists t, convert_expr t e1 /\ typecheck tc_env t cont_Bool *)
    assert (Hc: exists t, convert_expr t e1 /\ typecheck tc_env t cont_Bool).
      { apply (IHe1 fv1 c_fv c_T c_C cont_Bool Htie1 Hsubc Henv). }
    (* exists t, convert_expr t e2 /\ typecheck tc_env t T *)
    assert (He1: exists t, convert_expr t e2 /\ typecheck tc_env t T).
      { apply (IHe2 c_fv e1_fv S e1_C T Htie2 Hsube1 Henv). }
    (* exists t, convert_expr t e3 /\ typecheck tc_env t T *)
    assert (He2: exists t, convert_expr t e3 /\ typecheck tc_env t T).
      { apply (IHe3 e1_fv fv2 e2_T e2_C T Htie3 Hsube2 Henv). }
    destruct Hc as [c' [Hce Htc]].
    destruct He1 as [e1' [Hce1 Htc1]].
    destruct He2 as [e2' [Hce2 Htc2]].
    exists (t_If c' e1' e2'). split.
      * apply CE_If; assumption.
      * apply TC_If; assumption.
  (* ut_Fun *)
  - admit.
  (* ut_Call *)
  - admit.
  (* ut_Binop *)
  - (* b = op_Plus \/ b = op_Minus *)
    (* T = cont_Num *)
    rewrite app_substs_form_num in Hsubconv. inverts Hsubconv.
    (* solution sub e1_C *)
    assert (Hsol_e1_C: solution sub e1_C).
      { apply (solution_constr_concat sub e1_C [(e2_T, inft_Num); (e1_T, inft_Num)]).
        apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Num); (e1_T, inft_Num)])).
        assumption. }
    (* solution sub e2_C *)
    assert (Hsol_e2_C: solution sub e2_C).
      { apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Num); (e1_T, inft_Num)])).
        assumption. }
    (* convert_type (app_substs sub e1_T) cont_Num *)
    assert (Hsol_e1_T: solution sub [(e1_T, inft_Num)]).
      { apply (solution_constr_concat sub [(e2_T, inft_Num)] [(e1_T, inft_Num)]).
        apply (solution_constr_concat sub e1_C [(e2_T, inft_Num); (e1_T, inft_Num)]).
        apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Num); (e1_T, inft_Num)])).
        assumption. }
    inverts Hsol_e1_T as He1_num.
    assert (Hsubsts_e1_T: convert_type (app_substs sub e1_T) cont_Num).
      { rewrite He1_num, app_substs_form_num. apply CT_Num. }
    (* convert_type (app_substs sub e2_T) cont_Num *)
    assert (Hsol_e2_T: solution sub [(e2_T, inft_Num)]).
      { apply (solution_constr_concat sub [(e2_T, inft_Num)] [(e1_T, inft_Num)]).
        apply (solution_constr_concat sub e1_C [(e2_T, inft_Num); (e1_T, inft_Num)]).
        apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Num); (e1_T, inft_Num)])).
        assumption. }
    inverts Hsol_e2_T as He2_num.
    assert (Hsubsts_e2_T: convert_type (app_substs sub e2_T) cont_Num).
      { rewrite He2_num, app_substs_form_num. apply CT_Num. }
    (* exists s, solution s e1_C /\ convert_type (app_substs s e1_T) cont_Num *)
    assert (Hsube1: exists s, solution s e1_C /\ convert_type (app_substs s e1_T) cont_Num).
      { exists sub. split; assumption. }
    (* exists s, solution s e2_C /\ convert_type (app_substs s e2_T) cont_Num *)
    assert (Hsube2: exists s, solution s e2_C /\ convert_type (app_substs s e2_T) cont_Num).
      { exists sub. split; assumption. }
    (* exists t, convert_expr t e1 /\ typecheck tc_env t cont_Num *)
    assert (He1: exists t, convert_expr t e1 /\ typecheck tc_env t cont_Num).
      { apply (IHe1 fv1 e1_fv e1_T e1_C cont_Num Htie1 Hsube1 Henv). }
    (* exists t, convert_expr t e2 /\ typecheck tc_env t cont_Num *)
    assert (He2: exists t, convert_expr t e2 /\ typecheck tc_env t cont_Num).
      { apply (IHe2 e1_fv fv2 e2_T e2_C cont_Num Htie2 Hsube2 Henv). }
    destruct He1 as [e1' [Hce1 Htc1]]. destruct He2 as [e2' [Hce2 Htc2]].
    exists (t_Binop b e1' e2'). split.
      * apply CE_Binop; assumption.
      * apply TC_Binop_nnn; assumption.
  - (* b = op_Eq \/ b = op_Neq *)
    (* T = cont_Bool *)
    rewrite app_substs_form_bool in Hsubconv. inverts Hsubconv.
    (* solution sub e1_C *)
    assert (Hsol_e1_C: solution sub e1_C).
      { apply (solution_constr_concat sub e1_C [(e2_T, inft_Num); (e1_T, inft_Num)]).
        apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Num); (e1_T, inft_Num)])).
        assumption. }
    (* solution sub e2_C *)
    assert (Hsol_e2_C: solution sub e2_C).
      { apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Num); (e1_T, inft_Num)])).
        assumption. }
    (* convert_type (app_substs sub e1_T) cont_Num *)
    assert (Hsol_e1_T: solution sub [(e1_T, inft_Num)]).
      { apply (solution_constr_concat sub [(e2_T, inft_Num)] [(e1_T, inft_Num)]).
        apply (solution_constr_concat sub e1_C [(e2_T, inft_Num); (e1_T, inft_Num)]).
        apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Num); (e1_T, inft_Num)])).
        assumption. }
    inverts Hsol_e1_T as He1_num.
    assert (Hsubsts_e1_T: convert_type (app_substs sub e1_T) cont_Num).
      { rewrite He1_num, app_substs_form_num. apply CT_Num. }
    (* convert_type (app_substs sub e2_T) cont_Num *)
    assert (Hsol_e2_T: solution sub [(e2_T, inft_Num)]).
      { apply (solution_constr_concat sub [(e2_T, inft_Num)] [(e1_T, inft_Num)]).
        apply (solution_constr_concat sub e1_C [(e2_T, inft_Num); (e1_T, inft_Num)]).
        apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Num); (e1_T, inft_Num)])).
        assumption. }
    inverts Hsol_e2_T as He2_num.
    assert (Hsubsts_e2_T: convert_type (app_substs sub e2_T) cont_Num).
      { rewrite He2_num, app_substs_form_num. apply CT_Num. }
    (* exists s, solution s e1_C /\ convert_type (app_substs s e1_T) cont_Num *)
    assert (Hsube1: exists s, solution s e1_C /\ convert_type (app_substs s e1_T) cont_Num).
      { exists sub. split; assumption. }
    (* exists s, solution s e2_C /\ convert_type (app_substs s e2_T) cont_Num *)
    assert (Hsube2: exists s, solution s e2_C /\ convert_type (app_substs s e2_T) cont_Num).
      { exists sub. split; assumption. }
    (* exists t, convert_expr t e1 /\ typecheck tc_env t cont_Num *)
    assert (He1: exists t, convert_expr t e1 /\ typecheck tc_env t cont_Num).
      { apply (IHe1 fv1 e1_fv e1_T e1_C cont_Num Htie1 Hsube1 Henv). }
    (* exists t, convert_expr t e2 /\ typecheck tc_env t cont_Num *)
    assert (He2: exists t, convert_expr t e2 /\ typecheck tc_env t cont_Num).
      { apply (IHe2 e1_fv fv2 e2_T e2_C cont_Num Htie2 Hsube2 Henv). }
    destruct He1 as [e1' [Hce1 Htc1]]. destruct He2 as [e2' [Hce2 Htc2]].
    exists (t_Binop b e1' e2'). split.
      * apply CE_Binop; assumption.
      * apply TC_Binop_nnb; assumption.
  - (* b = op_And \/ b = op_Or *)
    (* T = cont_Bool *)
    rewrite app_substs_form_bool in Hsubconv. inverts Hsubconv.
    (* solution sub e1_C *)
    assert (Hsol_e1_C: solution sub e1_C).
      { apply (solution_constr_concat sub e1_C [(e2_T, inft_Bool); (e1_T, inft_Bool)]).
        apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Bool); (e1_T, inft_Bool)])).
        assumption. }
    (* solution sub e2_C *)
    assert (Hsol_e2_C: solution sub e2_C).
      { apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Bool); (e1_T, inft_Bool)])).
        assumption. }
    (* convert_type (app_substs sub e1_T) cont_Bool *)
    assert (Hsol_e1_T: solution sub [(e1_T, inft_Bool)]).
      { apply (solution_constr_concat sub [(e2_T, inft_Bool)] [(e1_T, inft_Bool)]).
        apply (solution_constr_concat sub e1_C [(e2_T, inft_Bool); (e1_T, inft_Bool)]).
        apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Bool); (e1_T, inft_Bool)])).
        assumption. }
    inverts Hsol_e1_T as He1_bool.
    assert (Hsubsts_e1_T: convert_type (app_substs sub e1_T) cont_Bool).
      { rewrite He1_bool, app_substs_form_bool. apply CT_Bool. }
    (* convert_type (app_substs sub e2_T) cont_Bool *)
    assert (Hsol_e2_T: solution sub [(e2_T, inft_Bool)]).
      { apply (solution_constr_concat sub [(e2_T, inft_Bool)] [(e1_T, inft_Bool)]).
        apply (solution_constr_concat sub e1_C [(e2_T, inft_Bool); (e1_T, inft_Bool)]).
        apply (solution_constr_concat sub e2_C (e1_C ++ [(e2_T, inft_Bool); (e1_T, inft_Bool)])).
        assumption. }
    inverts Hsol_e2_T as He2_bool.
    assert (Hsubsts_e2_T: convert_type (app_substs sub e2_T) cont_Bool).
      { rewrite He2_bool, app_substs_form_bool. apply CT_Bool. }
    (* exists s, solution s e1_C /\ convert_type (app_substs s e1_T) cont_Bool *)
    assert (Hsube1: exists s, solution s e1_C /\ convert_type (app_substs s e1_T) cont_Bool).
      { exists sub. split; assumption. }
    (* exists s, solution s e2_C /\ convert_type (app_substs s e2_T) cont_Bool *)
    assert (Hsube2: exists s, solution s e2_C /\ convert_type (app_substs s e2_T) cont_Bool).
      { exists sub. split; assumption. }
    (* exists t, convert_expr t e1 /\ typecheck tc_env t cont_Bool *)
    assert (He1: exists t, convert_expr t e1 /\ typecheck tc_env t cont_Bool).
      { apply (IHe1 fv1 e1_fv e1_T e1_C cont_Bool Htie1 Hsube1 Henv). }
    (* exists t, convert_expr t e2 /\ typecheck tc_env t cont_Bool *)
    assert (He2: exists t, convert_expr t e2 /\ typecheck tc_env t cont_Bool).
      { apply (IHe2 e1_fv fv2 e2_T e2_C cont_Bool Htie2 Hsube2 Henv). }
    destruct He1 as [e1' [Hce1 Htc1]]. destruct He2 as [e2' [Hce2 Htc2]].
    exists (t_Binop b e1' e2'). split.
      * apply CE_Binop; assumption.
      * apply TC_Binop_bbb; assumption.
  (* ut_Cons *)
  - (* solution sub hd_C *)
    assert (Hsol_hd_C: solution sub hd_C).
      { apply (solution_constr_concat sub hd_C [(tl_T, inft_List hd_T)]).
        apply (solution_constr_concat sub tl_C (hd_C ++ [(tl_T, inft_List hd_T)])).
        assumption. }
    (* solution sub tl_C *)
    assert (Hsol_tl_C: solution sub tl_C).
      { apply (solution_constr_concat sub tl_C (hd_C ++ [(tl_T, inft_List hd_T)])).
        assumption. }
    (* convert_type (app_substs sub hd_T) l_t *)
    assert (Hsol_tl_T_hd_T: solution sub [(tl_T, inft_List hd_T)]).
      { apply (solution_constr_concat sub hd_C [(tl_T, inft_List hd_T)]).
        apply (solution_constr_concat sub tl_C (hd_C ++ [(tl_T, inft_List hd_T)])).
        assumption. }
    inverts Hsol_tl_T_hd_T.
    rewrite (app_substs_sub_list sub hd_T) in Hsubconv. inverts keep Hsubconv as Hsubsts_hd_T.
    (* convert_type (app_substs sub tl_T) (cont_List l_t) *)
    assert (Hsubsts_lt_T: convert_type (app_substs sub tl_T) (cont_List l_t)).
      { rewrite H2. rewrite (app_substs_sub_list sub hd_T). apply CT_List. assumption. }
    (* exists s, solution s hd_C /\ convert_type (app_substs s hd_T) l_t *)
    assert (Hsube1: exists s, solution s hd_C /\ convert_type (app_substs s hd_T) l_t).
      { exists sub. split; assumption. }
    (* exists s, solution s tl_C /\ convert_type (app_substs s tl_T) (cont_List l_t) *)
    assert (Hsube2: exists s, solution s tl_C /\ convert_type (app_substs s tl_T) (cont_List l_t)).
      { exists sub. split; assumption. }
    (* exists t, convert_expr t e1 /\ typecheck tc_env t l_t *)
    assert (He1: exists t, convert_expr t e1 /\ typecheck tc_env t l_t).
      { apply (IHe1 fv1 hd_fv hd_T hd_C l_t Htie1 Hsube1 Henv). }
    (* exists t, convert_expr t e2 /\ typecheck tc_env t (cont_List l_t) *)
    assert (He2: exists t, convert_expr t e2 /\ typecheck tc_env t (cont_List l_t) ).
      { apply (IHe2 hd_fv fv2 tl_T tl_C (cont_List l_t) Htie2 Hsube2 Henv). }
    destruct He1 as [e1' [Hce1 Htc1]]. destruct He2 as [e2' [Hce2 Htc2]].
    exists (t_Cons e1' e2'). split.
      * apply CE_Cons; assumption.
      * apply TC_Cons; assumption.
  (* ut_Nil *)
  - assert (Hflist: exists t', app_substs sub (inft_List (inft_Var (Id fv1))) = inft_List t').
      { apply (app_substs_form_list sub (inft_Var (Id fv1))). }
    inverts Hflist. rewrite H in Hsubconv. inverts Hsubconv.
    exists (t_Nil l_t). split.
    * apply CE_Nil.
    * apply TC_Nil.
Admitted.
