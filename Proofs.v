Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Arith.

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

(*
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
*)

(* substs *)
Lemma subst_concrete_type :
  forall s T, concrete_type T -> subst s T = T.
Proof.
  introv Hvt.
  induction T.
  - reflexivity.
  - reflexivity.
  - inverts Hvt. simpl.
    apply IHT1 in H1.
    apply IHT2 in H2.
    rewrite H1, H2.
    reflexivity.
  - inverts Hvt. simpl.
    apply IHT in H0.
    rewrite H0.
    reflexivity.
  - inverts Hvt.
Qed.

Lemma subst_form_any :
  forall s t, exists t', subst s t = t'.
Proof.
  introv.
  induction t.
  - exists TNum. reflexivity.
  - exists TBool. reflexivity.
  - destruct IHt1 as [t1' H1]. destruct IHt2 as [t2' H2].
    exists (TFun t1' t2'). simpl.
    rewrite H1, H2. reflexivity.
  - destruct IHt as [t'' H].
    exists (TList t''). simpl.
    rewrite H. reflexivity.
  - destruct s as [x y]. simpl. destruct beq_id.
    * exists y. reflexivity.
    * exists (TVar i). reflexivity.
Qed.

Lemma subst_form_num :
  forall s, subst s TNum = TNum.
Proof. reflexivity. Qed.

Lemma subst_form_bool :
  forall s, subst s TBool = TBool.
Proof. reflexivity. Qed.

Lemma subst_form_list :
  forall s t, exists t', subst s (TList t) = TList t'.
Proof.
  introv.
  simpl.
  assert (H: exists t'', subst s t = t'').
    { apply subst_form_any. }
  destruct H as [t'' H]. exists t''. rewrite H. reflexivity.
Qed.

Lemma subst_form_fun :
  forall s t1 t2, exists t1' t2', subst s (TFun t1 t2) = TFun t1' t2'.
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
Lemma app_substs_concrete_type :
  forall s T, concrete_type T -> app_substs s T = T.
Proof.
  introv H.
  induction s as [|hd tl].
  - reflexivity.
  - destruct T.
    * simpl. rewrite IHtl. apply subst_concrete_type. assumption.
    * simpl. rewrite IHtl. apply subst_concrete_type. assumption.
    * simpl. rewrite IHtl. apply subst_concrete_type. assumption.
    * simpl. rewrite IHtl. apply subst_concrete_type. assumption.
    * inverts H.
Qed.

Lemma app_substs_form_num :
  forall s, app_substs s TNum = TNum.
Proof.
  introv.
  apply (app_substs_concrete_type s TNum).
  apply CT_Num.
Qed.

Lemma app_substs_form_bool :
  forall s, app_substs s TBool = TBool.
Proof.
  introv.
  apply (app_substs_concrete_type s TBool).
  apply CT_Bool.
Qed.

Lemma app_substs_sub_list :
  forall s t, app_substs s (TList t) = TList (app_substs s t).
Proof.
  introv.
  induction s as [|hd tl].
  - reflexivity.
  - simpl. rewrite IHtl. simpl. reflexivity.
Qed.

Lemma app_substs_form_list :
  forall s t, exists t', app_substs s (TList t) = TList t'.
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
  forall s t1 t2, app_substs s (TFun t1 t2) = TFun (app_substs s t1) (app_substs s t2).
Proof.
  introv.
  induction s as [|hd tl].
  - reflexivity.
  - simpl. rewrite IHtl. simpl. reflexivity.
Qed.

Lemma app_substs_form_fun :
  forall s t1 t2, exists t1' t2', app_substs s (TFun t1 t2) = TFun t1' t2'.
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
    t_env
    t T
    e S C fv1 fv2,
  convert_expr t e ->
  typecheck t_env t T ->
  typeinf t_env fv1 e (fv2, S, C) ->
  (exists s, solution s C /\ app_substs s S = T).
Proof.
  induction t;
  introv Hc Htc Hti .
  - inverts Hc. inverts Hti. inverts Htc.
    exists (@nil (id * t_type) % type). simpl. split.
    * apply SOL_Empty.
    * reflexivity.
  - inverts Hc. inverts Hti. inverts Htc.
    exists (@nil (id * t_type) % type). simpl. split.
    * apply SOL_Empty.
    * reflexivity.
  - inverts Hc. inverts Hti. inverts Htc.
    exists (@nil (id * t_type) % type). simpl. split.
    * apply SOL_Empty.
    * rewrite H1 in H3. inverts H3. reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - inverts Hc. inverts Hti. inverts Htc.
    exists [(Id fv1, t)]. split.
    * apply SOL_Empty.
    * simpl. rewrite <- beq_nat_refl. reflexivity.
Admitted.

Theorem typeinference_completeness :
  forall
    t_env e fv1 fv2 S C,
  typeinf t_env fv1 e (fv2, S, C) ->
  (exists s, solution s C) ->
  (exists t T, convert_expr t e /\ typecheck t_env t T).
Proof.
  induction e;
  introv Hti Hsub;
  destruct Hsub as [sub Hsubsol];
  inverts Hti as Htie1 Htie2 Htie3; sort.
  (* ut_Num *)
  - exists (t_Num n) TNum. split.
    * apply CE_Num.
    * apply TC_Num.
  (* ut_Bool *)
  - exists (t_Bool b) TBool. split.
    * apply CE_Bool.
    * apply TC_Bool.
  (* ut_Var *)
  - exists (t_Var i) S. split.
    * apply CE_Var.
    * apply TC_Var. assumption.
  (* ut_If *)
  - admit.
(*
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
*)
  (* ut_Fun *)
  - admit.
  (* ut_Call *)
  - admit.
  (* ut_Binop *)
  - admit. (* b = op_Plus \/ b = op_Minus *)
(*
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
*)
  - admit. (* b = op_Eq \/ b = op_Neq *)
(*
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
*)
  - admit. (* b = op_And \/ b = op_Or *)
(*
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
*)
  (* ut_Cons *)
  - admit.
(*
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
*)
  (* ut_Nil *)
  - exists (t_Nil TNum) (TList TNum). split.
    * apply CE_Nil.
    * apply TC_Nil.
Admitted.
