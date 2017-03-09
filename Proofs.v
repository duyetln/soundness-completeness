Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Arith.
Require Import FunctionalExtensionality.

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

(* app_sub_to_type *)
Example app_sub_to_type_ex1 : app_sub_to_type (update empty_substs (Id 1) TNum) (TFun (TVar (Id 1)) TNum) = TFun TNum TNum.
Proof. reflexivity. Qed.

Example app_sub_to_type_ex2 : app_sub_to_type (update (update empty_substs (Id 1) TNum) (Id 2) TBool) (TFun (TVar (Id 1)) (TVar (Id 2))) = TFun TNum TBool.
Proof. reflexivity. Qed.

Lemma app_sub_to_concrete_type :
  forall s T, concrete_type T -> app_sub_to_type s T = T.
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

(* satisfy *)
Example satisfy_ex1 :
  satisfy
    (update (update (update empty_substs (Id 1) TNum) (Id 2) TNum) (Id 3) TNum)
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

Lemma satisfy_constr_concat :
  forall s C1 C2, satisfy s C1 /\ satisfy s C2 <-> satisfy s (C1 ++ C2).
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

(* app_sub_to_env *)
Lemma app_sub_to_update_env :
  forall sub env i t,
    app_sub_to_env sub (update env i t) = update (app_sub_to_env sub env) i (app_sub_to_type sub t).
Proof.
  intros.
  unfold app_sub_to_env.
  unfold update.
  unfold t_update.
  apply functional_extensionality_dep.
  intro x'.
  destruct (beq_id i x').
  - reflexivity.
  - reflexivity.
Qed.

(* delete *)
Example delete_ex1 :
  (delete
  (update (update (update empty_substs (Id 1) TNum) (Id 2) TNum) (Id 3) TNum)
  [Id 2]) (Id 2) = None.
Proof.
  reflexivity.
Qed.

Lemma delete_x_sub_none :
  forall X x sub, sub x = None -> (delete sub X) x = None.
Proof.
  induction X as [|x' X'];
  introv Hsub.
  - simpl. assumption.
  - simpl. destruct (sub x').
    + apply (IHX' x (t_update sub x' None)). destruct (beq_id x' x) eqn:Hid.
      * apply beq_id_true_iff in Hid.
        rewrite Hid.
        apply t_update_eq.
      * apply beq_id_false_iff in Hid.
        rewrite <- Hsub.
        apply t_update_neq.
        assumption.
    + apply (IHX' x sub Hsub).
Qed.

Lemma delete_x_in_list :
  forall X x sub,
    In x X ->
    (delete sub X) x = None.
Proof.
  induction X as [|x' X'];
  introv Hx;
  inverts Hx;
  simpl.
  - destruct (sub x) eqn:Hsub.
    + apply (delete_x_sub_none X' x (t_update sub x None)). apply t_update_eq.
    + apply (delete_x_sub_none X' x sub Hsub).
  - destruct (sub x') eqn:Hsub.
    + apply (IHX' x (t_update sub x' None) H).
    + apply (IHX' x sub H).
Qed.


(* ################################################################# *)
(* Main goals *)

Theorem typeinference_soundness :
  forall
    e ti_env fv1 fv2 S C X
    sub
    t tc_env T,
  typeinf ti_env fv1 e (fv2, S, C, X) ->
  satisfy sub C ->
  app_sub_to_expr sub e = t ->
  app_sub_to_type sub S = T ->
  app_sub_to_env sub ti_env = tc_env ->
  typecheck tc_env t T.
Proof.
  induction e;
  introv Hti Hsat Hexpr Htype Henv;
  try (inverts Hti as Htie1 Htie2 Htie3; simpl in Hexpr; simpl in Htype; simpl in Henv);
  sort.
  (* ENum *)
  - rewrite <- Hexpr, <- Htype, <- Henv. apply TC_Num.
  (* EBool *)
  - rewrite <- Hexpr, <- Htype, <- Henv. apply TC_Bool.
  (* EVar *)
  - rewrite <- Hexpr, <- Htype, <- Henv. apply TC_Var.
    unfold app_sub_to_env. rewrite Htie1. reflexivity.

  (* EIf *)
  - (* satisfy sub c_C *)
    assert (Hsat_c_C: satisfy sub c_C).
      { apply (satisfy_constr_concat sub c_C [(S, e2_T); (c_T, TBool)]).
        apply (satisfy_constr_concat sub e1_C (c_C ++ [(S, e2_T); (c_T, TBool)])).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, TBool)])).
        assumption. }
    (* satisfy sub e1_C *)
    assert (Hsat_e1_C: satisfy sub e1_C).
      { apply (satisfy_constr_concat sub e1_C (c_C ++ [(S, e2_T); (c_T, TBool)])).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, TBool)])).
        assumption. }
    (* satisfy sub e2_C *)
    assert (Hsat_e2_C: satisfy sub e2_C).
      { apply (satisfy_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, TBool)])).
        assumption. }
    (* app_sub_to_type sub c_T = TBool *)
    assert (Hsat_c_T_TBool: satisfy sub [(c_T, TBool)]).
      { apply (satisfy_constr_concat sub [(S, e2_T)] [(c_T, TBool)]).
        apply (satisfy_constr_concat sub c_C [(S, e2_T); (c_T, TBool)]).
        apply (satisfy_constr_concat sub e1_C (c_C ++ [(S, e2_T); (c_T, TBool)])).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, TBool)])).
        assumption. }
    inverts Hsat_c_T_TBool as Happsub_c_T_TBool Tmp. clear Tmp.
    simpl in Happsub_c_T_TBool.
    (* app_sub_to_type sub S = app_sub_to_type sub e2_T *)
    assert (Hsat_S_e2_T: satisfy sub [(S, e2_T)]).
      { apply (satisfy_constr_concat sub [(S, e2_T)] [(c_T, TBool)]).
        apply (satisfy_constr_concat sub c_C [(S, e2_T); (c_T, TBool)]).
        apply (satisfy_constr_concat sub e1_C (c_C ++ [(S, e2_T); (c_T, TBool)])).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ c_C ++ [(S, e2_T); (c_T, TBool)])).
        assumption. }
    inverts Hsat_S_e2_T as Happsub_S_e2_T Tmp. clear Tmp.
    simpl in Happsub_S_e2_T.
    (* typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub c_T) *)
    assert (Hc: typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub c_T)).
      { apply (IHe1 ti_env fv1 c_fv c_T c_C c_X sub (app_sub_to_expr sub e1) tc_env (app_sub_to_type sub c_T));
        try assumption; reflexivity. }
    (* typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub S) *)
    assert (He1: typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub S)).
      { apply (IHe2 ti_env c_fv e1_fv S e1_C e1_X sub (app_sub_to_expr sub e2) tc_env (app_sub_to_type sub S));
        try assumption; reflexivity. }
    (* typecheck tc_env (app_sub_to_expr sub e3) (app_sub_to_type sub e2_T) *)
    assert (He2: typecheck tc_env (app_sub_to_expr sub e3) (app_sub_to_type sub e2_T)).
      { apply (IHe3 ti_env e1_fv fv2 e2_T e2_C e2_X sub (app_sub_to_expr sub e3) tc_env (app_sub_to_type sub e2_T));
        try assumption; reflexivity. }
    rewrite <- Hexpr, <- Htype. apply TC_If.
      * rewrite <- Happsub_c_T_TBool. assumption.
      * assumption.
      * rewrite Happsub_S_e2_T. assumption.

  (* EFun *)
  - (* typecheck (update ti_env i t) (app_sub_to_expr sub e) (app_sub_to_type sub e_T) *)
    assert (He: typecheck (app_sub_to_env sub (update ti_env i t)) (app_sub_to_expr sub e) (app_sub_to_type sub e_T)).
      { apply (IHe (update ti_env i t) fv1 fv2 e_T C X sub (app_sub_to_expr sub e) (app_sub_to_env sub (update ti_env i t)) (app_sub_to_type sub e_T));
        try assumption; reflexivity. }
    rewrite <- Hexpr, <- Htype. apply TC_Fun.
    rewrite <- Henv, <- (app_sub_to_update_env sub ti_env i t).
    assumption.

  (* ECall *)
  - (* satisfy sub f_C *)
    assert (Hsat_f_C: satisfy sub f_C).
      { apply (satisfy_constr_concat sub f_C [(f_T, TFun e_T (TVar (Id e_fv)))]).
        apply (satisfy_constr_concat sub e_C (f_C ++ [(f_T, TFun e_T (TVar (Id e_fv)))])).
        assumption. }
    (* satisfy sub e_C *)
    assert (Hsat_e_C: satisfy sub e_C).
      { apply (satisfy_constr_concat sub e_C (f_C ++ [(f_T, TFun e_T (TVar (Id e_fv)))])).
        assumption. }
    (* app_sub_to_type sub f_T = app_sub_to_type (TFun e_T (TVar (Id e_fv))) *)
    assert (Hsat_f_T_TFun: satisfy sub [(f_T, TFun e_T (TVar (Id e_fv)))]).
      { apply (satisfy_constr_concat sub f_C [(f_T, TFun e_T (TVar (Id e_fv)))]).
        apply (satisfy_constr_concat sub e_C (f_C ++ [(f_T, TFun e_T (TVar (Id e_fv)))])).
        assumption. }
    inverts Hsat_f_T_TFun as Happsub_f_T_TFun Tmp. clear Tmp.
    simpl in Happsub_f_T_TFun.
    (* typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub f_T) *)
    assert (Hf: typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub f_T)).
      { apply (IHe1 ti_env fv1 f_fv f_T f_C f_X sub (app_sub_to_expr sub e1) tc_env (app_sub_to_type sub f_T));
        try assumption; reflexivity. }
    (* typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub e_T) *)
    assert (He: typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub e_T)).
      { apply (IHe2 ti_env f_fv e_fv e_T e_C e_X sub (app_sub_to_expr sub e2) tc_env (app_sub_to_type sub e_T));
        try assumption; reflexivity. }
    rewrite <- Hexpr, <- Htype. apply TC_Call with (e_T := (app_sub_to_type sub e_T)).
      * rewrite <- Happsub_f_T_TFun. assumption.
      * assumption.

  (* EBinop *)
  - (* b = OpPlus \/ b = OpMinus *)
    (* satisfy sub e1_C *)
    assert (Hsat_e1_C: satisfy sub e1_C).
      { apply (satisfy_constr_concat sub e1_C [(e2_T, TNum); (e1_T, TNum)]).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TNum); (e1_T, TNum)])).
        assumption. }
    (* satisfy sub e2_C *)
    assert (Hsat_e2_C: satisfy sub e2_C).
      { apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TNum); (e1_T, TNum)])).
        assumption. }
    (* app_sub_to_type sub e1_T = TNum *)
    assert (Hsat_e1_T_TNum: satisfy sub [(e1_T, TNum)]).
      { apply (satisfy_constr_concat sub [(e2_T, TNum)] [(e1_T, TNum)]).
        apply (satisfy_constr_concat sub e1_C [(e2_T, TNum); (e1_T, TNum)]).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TNum); (e1_T, TNum)])).
        assumption. }
    inverts Hsat_e1_T_TNum as Happsub_e1_T_TNum Tmp. clear Tmp.
    simpl in Happsub_e1_T_TNum.
    (* app_sub_to_type sub e2_T = TNum *)
    assert (Hsat_e2_T_TNum: satisfy sub [(e2_T, TNum)]).
      { apply (satisfy_constr_concat sub [(e2_T, TNum)] [(e1_T, TNum)]).
        apply (satisfy_constr_concat sub e1_C [(e2_T, TNum); (e1_T, TNum)]).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TNum); (e1_T, TNum)])).
        assumption. }
    inverts Hsat_e2_T_TNum as Happsub_e2_T_TNum Tmp. clear Tmp.
    simpl in Happsub_e2_T_TNum.
    (* typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub e1_T) *)
    assert (He1: typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub e1_T)).
      { apply (IHe1 ti_env fv1 e1_fv e1_T e1_C e1_X sub (app_sub_to_expr sub e1) tc_env (app_sub_to_type sub e1_T));
        try assumption; reflexivity. }
    (* typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub e2_T) *)
    assert (He2: typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub e2_T)).
      { apply (IHe2 ti_env e1_fv fv2 e2_T e2_C e2_X sub (app_sub_to_expr sub e2) tc_env (app_sub_to_type sub e2_T));
        try assumption; reflexivity. }
    rewrite <- Hexpr, <- Htype. apply TC_Binop_nnn.
      * assumption.
      * rewrite <- Happsub_e1_T_TNum. assumption.
      * rewrite <- Happsub_e2_T_TNum. assumption.
  - (* b = OpEq \/ b = OpNeq *)
    (* satisfy sub e1_C *)
    assert (Hsat_e1_C: satisfy sub e1_C).
      { apply (satisfy_constr_concat sub e1_C [(e2_T, TNum); (e1_T, TNum)]).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TNum); (e1_T, TNum)])).
        assumption. }
    (* satisfy sub e2_C *)
    assert (Hsat_e2_C: satisfy sub e2_C).
      { apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TNum); (e1_T, TNum)])).
        assumption. }
    (* app_sub_to_type sub e1_T = TNum *)
    assert (Hsat_e1_T_TNum: satisfy sub [(e1_T, TNum)]).
      { apply (satisfy_constr_concat sub [(e2_T, TNum)] [(e1_T, TNum)]).
        apply (satisfy_constr_concat sub e1_C [(e2_T, TNum); (e1_T, TNum)]).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TNum); (e1_T, TNum)])).
        assumption. }
    inverts Hsat_e1_T_TNum as Happsub_e1_T_TNum Tmp. clear Tmp.
    simpl in Happsub_e1_T_TNum.
    (* app_sub_to_type sub e2_T = TNum *)
    assert (Hsat_e2_T_TNum: satisfy sub [(e2_T, TNum)]).
      { apply (satisfy_constr_concat sub [(e2_T, TNum)] [(e1_T, TNum)]).
        apply (satisfy_constr_concat sub e1_C [(e2_T, TNum); (e1_T, TNum)]).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TNum); (e1_T, TNum)])).
        assumption. }
    inverts Hsat_e2_T_TNum as Happsub_e2_T_TNum Tmp. clear Tmp.
    simpl in Happsub_e2_T_TNum.
    (* typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub e1_T) *)
    assert (He1: typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub e1_T)).
      { apply (IHe1 ti_env fv1 e1_fv e1_T e1_C e1_X sub (app_sub_to_expr sub e1) tc_env (app_sub_to_type sub e1_T));
        try assumption; reflexivity. }
    (* typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub e2_T) *)
    assert (He2: typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub e2_T)).
      { apply (IHe2 ti_env e1_fv fv2 e2_T e2_C e2_X sub (app_sub_to_expr sub e2) tc_env (app_sub_to_type sub e2_T));
        try assumption; reflexivity. }
    rewrite <- Hexpr, <- Htype. apply TC_Binop_nnb.
      * assumption.
      * rewrite <- Happsub_e1_T_TNum. assumption.
      * rewrite <- Happsub_e2_T_TNum. assumption.
  - (* b = OpAnd \/ b = OpOr *)
    (* satisfy sub e1_C *)
    assert (Hsat_e1_C: satisfy sub e1_C).
      { apply (satisfy_constr_concat sub e1_C [(e2_T, TBool); (e1_T, TBool)]).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TBool); (e1_T, TBool)])).
        assumption. }
    (* satisfy sub e2_C *)
    assert (Hsat_e2_C: satisfy sub e2_C).
      { apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TBool); (e1_T, TBool)])).
        assumption. }
    (* app_sub_to_type sub e1_T = TBool *)
    assert (Hsat_e1_T_TBool: satisfy sub [(e1_T, TBool)]).
      { apply (satisfy_constr_concat sub [(e2_T, TBool)] [(e1_T, TBool)]).
        apply (satisfy_constr_concat sub e1_C [(e2_T, TBool); (e1_T, TBool)]).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TBool); (e1_T, TBool)])).
        assumption. }
    inverts Hsat_e1_T_TBool as Happsub_e1_T_TBool Tmp. clear Tmp.
    simpl in Happsub_e1_T_TBool.
    (* app_sub_to_type sub e2_T = TBool *)
    assert (Hsat_e2_T_TBool: satisfy sub [(e2_T, TBool)]).
      { apply (satisfy_constr_concat sub [(e2_T, TBool)] [(e1_T, TBool)]).
        apply (satisfy_constr_concat sub e1_C [(e2_T, TBool); (e1_T, TBool)]).
        apply (satisfy_constr_concat sub e2_C (e1_C ++ [(e2_T, TBool); (e1_T, TBool)])).
        assumption. }
    inverts Hsat_e2_T_TBool as Happsub_e2_T_TBool Tmp. clear Tmp.
    simpl in Happsub_e2_T_TBool.
    (* typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub e1_T) *)
    assert (He1: typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub e1_T)).
      { apply (IHe1 ti_env fv1 e1_fv e1_T e1_C e1_X sub (app_sub_to_expr sub e1) tc_env (app_sub_to_type sub e1_T));
        try assumption; reflexivity. }
    (* typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub e2_T) *)
    assert (He2: typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub e2_T)).
      { apply (IHe2 ti_env e1_fv fv2 e2_T e2_C e2_X sub (app_sub_to_expr sub e2) tc_env (app_sub_to_type sub e2_T));
        try assumption; reflexivity. }
    rewrite <- Hexpr, <- Htype. apply TC_Binop_bbb.
      * assumption.
      * rewrite <- Happsub_e1_T_TBool. assumption.
      * rewrite <- Happsub_e2_T_TBool. assumption.
  (* ECons *)
  - (* satisfy sub hd_C *)
    assert (Hsat_hd_C: satisfy sub hd_C).
      { apply (satisfy_constr_concat sub hd_C [(tl_T, TList hd_T)]).
        apply (satisfy_constr_concat sub tl_C (hd_C ++ [(tl_T, TList hd_T)])).
        assumption. }
    (* satisfy sub tl_C *)
    assert (Hsat_tl_C: satisfy sub tl_C).
      { apply (satisfy_constr_concat sub tl_C (hd_C ++ [(tl_T, TList hd_T)])).
        assumption. }
    (* app_sub_to_type sub tl_T = TList (app_sub_to_type sub hd_T) *)
    assert (Hsat_tl_T_hd_T: satisfy sub [(tl_T, TList hd_T)]).
      { apply (satisfy_constr_concat sub hd_C [(tl_T, TList hd_T)]).
        apply (satisfy_constr_concat sub tl_C (hd_C ++ [(tl_T, TList hd_T)])).
        assumption. }
    inverts Hsat_tl_T_hd_T as Happsub_tl_T_hd_T Tmp. clear Tmp.
    simpl in Happsub_tl_T_hd_T.
    (* typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub hd_T) *)
    assert (He1: typecheck tc_env (app_sub_to_expr sub e1) (app_sub_to_type sub hd_T)).
      { apply (IHe1 ti_env fv1 hd_fv hd_T hd_C hd_X sub (app_sub_to_expr sub e1) tc_env (app_sub_to_type sub hd_T));
        try assumption; reflexivity. }
    (* typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub (TList hd_T)) *)
    assert (He2: typecheck tc_env (app_sub_to_expr sub e2) (app_sub_to_type sub tl_T)).
      { apply (IHe2 ti_env hd_fv fv2 tl_T tl_C tl_X sub (app_sub_to_expr sub e2) tc_env (app_sub_to_type sub tl_T));
        try assumption; reflexivity. }
    rewrite <- Hexpr, <- Htype. apply TC_Cons.
      * assumption.
      * rewrite <- Happsub_tl_T_hd_T. assumption.

  (* ENil *)
  - rewrite <- Hexpr, <- Htype. apply TC_Nil.
Qed.

(*
Theorem typeinference_completeness :
  forall
    t_env e fv1 fv2 S C,
  typeinf t_env fv1 e (fv2, S, C) ->
  (exists s, solution s C) ->
  (exists t T, convert_expr t e /\ typecheck t_env t T).
*)