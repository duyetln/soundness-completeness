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


(* misc *)
Lemma in_app_iff_prop :
  forall {T : Type } (l l' : list T) (P : T -> Prop),
    (forall i, In i (l ++ l') -> P i) <->
    (forall i, In i l -> P i) /\ (forall i, In i l' -> P i).
Proof.
  introv. split.
  - introv Hll'. split.
    * introv Hl.
      assert (Hll'': In i (l ++ l')).
        { apply in_app_iff. left. assumption. }
      apply (Hll' i Hll'').
    * introv Hl'.
      assert (Hll'': In i (l ++ l')).
        { apply in_app_iff. right. assumption. }
      apply (Hll' i Hll'').
  - introv Hll'. inverts Hll' as Hl Hl'.
    introv Hi. apply in_app_iff in Hi. destruct Hi as [Hil|Hil'].
    * apply (Hl i Hil).
    * apply (Hl' i Hil').
Qed.

Lemma app_non_nil :
  forall {T : Type} (l l' : list T),
    l <> [] -> (l ++ l') <> [].
Proof.
  introv Hl. intro.
  apply app_eq_nil in H.
  destruct H as [Hnl Hnl'].
  apply Hl. assumption.
Qed.

Lemma lt_n_n_1 :
  forall n, n < n + 1.
Proof.
  introv.
  assert (H: n + 0 < n + 1).
    { apply (plus_lt_compat_l 0 1 n).
      apply (Nat.lt_succ_diag_r 0). }
  rewrite <- (plus_n_O n) in H.
  assumption.
Qed.

Lemma lt_n_n :
  forall n, ~(n < n).
Proof.
  unfold not.
  introv H.
  apply (le_not_lt n n (le_n n)).
  assumption.
Qed.

Lemma and_factor :
  forall P Q R,
     P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  introv. split.
  - introv H. destruct H as [HP HQR]. destruct HQR as [HQ|HR].
    * left. split; assumption.
    * right. split; assumption.
  - introv H. destruct H as [HPQ|HPR].
    * destruct HPQ as [HP HQ]. split.
      + assumption.
      + left. assumption.
    * destruct HPR as [HP HR]. split.
      + assumption.
      + right. assumption.
Qed.

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
  apply SAT_NotEmpty.
  - reflexivity.
  - apply SAT_NotEmpty.
    * reflexivity.
    * apply SAT_NotEmpty.
      + reflexivity.
      + apply SAT_Empty.
Qed.

Lemma satisfy_constr_concat :
  forall s C1 C2, satisfy s C1 /\ satisfy s C2 <-> satisfy s (C1 ++ C2).
Proof.
  introv. split.
  - introv [HC1 HC2]. induction C1 as [|hd1 tl1].
    * simpl. assumption.
    * simpl. inverts HC1.
      apply SAT_NotEmpty.
      + assumption.
      + apply (IHtl1 H3).
  - introv H. induction C1 as [|hd1 tl1]; simpl in H.
    * split.
      + apply SAT_Empty.
      + assumption.
    * inverts H. apply IHtl1 in H4. inverts H4. split.
      + apply SAT_NotEmpty.
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

(* max_typevar *)
Lemma max_typevar_larger_fv :
  forall t fv,
    fv < max_typevar t fv + 1.
Proof.
  induction t;
  introv;
  simpl;
  try (apply (lt_n_n_1 fv)); unfold max_typevar; simpl.
  - rewrite (map_app (fun i : id => match i with | Id n => n end) (typevars t1) (typevars t2)).
    rewrite (fold_left_app (fun mx n : nat => max mx n)
              (map (fun i : id => match i with | Id n => n end) (typevars t1))
              (map (fun i : id => match i with | Id n => n end) (typevars t2))
              fv).
    fold (max_typevar t1 fv).
    fold (max_typevar t2 (max_typevar t1 fv)).
    assert (Hlt_fv_t1: fv < max_typevar t1 fv + 1).
      { apply (IHt1 fv). }
    rewrite Nat.add_1_r in Hlt_fv_t1. apply lt_n_Sm_le in Hlt_fv_t1.
    assert (Hlt_t1_t2: max_typevar t1 fv < max_typevar t2 (max_typevar t1 fv) + 1).
      { apply (IHt2 (max_typevar t1 fv)). }
    apply (Nat.le_lt_trans fv (max_typevar t1 fv) (max_typevar t2 (max_typevar t1 fv) + 1) Hlt_fv_t1 Hlt_t1_t2).
  - apply (IHt fv).
  - destruct i. destruct (Max.max_dec fv n) eqn:He.
    * rewrite e. apply (lt_n_n_1 fv).
    * assert (Hle_fv_n: fv <= Nat.max fv n).
        { apply (Max.le_max_l fv n). }
      rewrite e in Hle_fv_n.
      rewrite e.
      apply (Nat.le_lt_trans fv n (n + 1) Hle_fv_n (lt_n_n_1 n)).
Qed.

Lemma max_typevar_larger_typevar :
  forall t fv,
    (forall n, In (Id n) (typevars t) -> n <  max_typevar t fv + 1).
Proof.
  induction t;
  unfold max_typevar;
  simpl;
  introv Hin;
  simpl in Hin;
  try (inverts Hin as H').
  - rewrite (map_app (fun i : id => match i with | Id n0 => n0 end) (typevars t1) (typevars t2)).
    rewrite (fold_left_app (fun mx n : nat => max mx n)
              (map (fun i : id => match i with | Id n0 => n0 end) (typevars t1))
              (map (fun i : id => match i with | Id n0 => n0 end) (typevars t2))
              fv).
    fold (max_typevar t1 fv).
    fold (max_typevar t2 (max_typevar t1 fv)).
    apply in_app_or in Hin. destruct Hin as [Hint1|Hint2].
    * assert (Hlt_n_t1: n < max_typevar t1 fv + 1).
        { apply (IHt1 fv n Hint1). }
      rewrite Nat.add_1_r in Hlt_n_t1. apply lt_n_Sm_le in Hlt_n_t1.
      assert (Hlt_t1_t2: max_typevar t1 fv < max_typevar t2 (max_typevar t1 fv) + 1).
        { apply (max_typevar_larger_fv t2 (max_typevar t1 fv)). }
      apply (Nat.le_lt_trans n (max_typevar t1 fv) (max_typevar t2 (max_typevar t1 fv) + 1) Hlt_n_t1 Hlt_t1_t2).
    * apply (IHt2 (max_typevar t1 fv) n Hint2).
  - fold (max_typevar t fv). apply (IHt fv n Hin).
  - destruct (Max.max_dec fv n) eqn:He.
    * assert (Hle_n_fv: n <= Nat.max fv n).
        { apply (Max.le_max_r fv n). }
      rewrite e in Hle_n_fv.
      rewrite e.
      apply (Nat.le_lt_trans n fv (fv + 1) Hle_n_fv (lt_n_n_1 fv)).
    * rewrite e. apply (lt_n_n_1 n).
  - inverts H'.
Qed.

(* typevars *)
Example typevars_ex1 :
  typevars (TFun (TVar (Id 1)) (TList (TVar (Id 2)))) = [Id 1; Id 2].
Proof. reflexivity. Qed.

Example typevars_ex2 :
  typevars_from_constr
    [(TList (TVar (Id 1)), TList TNum); (TList (TVar (Id 3)), TList TNum); (TVar (Id 2), TNum)] =
    [Id 1; Id 3; Id 2].
Proof. reflexivity. Qed.

(* typeinf *)
Lemma typeinf_larger_fv :
  forall e t_env fv1 fv2 S C X,
    typeinf t_env fv1 e (fv2, S, C, X) -> fv1 < fv2.
Proof.
  induction e;
  introv Hti;
  inverts Hti as Htie1 Htie2 Htie3;
  try (apply (lt_n_n_1 fv1));
  sort.
  - apply (max_typevar_larger_fv S fv1).
  - assert (Hlt_fv1_c_fv: fv1 < c_fv).
      { apply (IHe1 t_env fv1 c_fv c_T c_C c_X Htie1). }
    assert (Hlt_c_fv_e1_fv: c_fv < e1_fv).
      { apply (IHe2 t_env c_fv e1_fv S e1_C e1_X Htie2). }
    assert (Hlt_e1_fv_fv2: e1_fv < fv2).
      { apply (IHe3 t_env e1_fv fv2 e2_T e2_C e2_X Htie3). }
    assert (Hlt_c_fv_fv2: c_fv < fv2).
      { apply (lt_trans c_fv e1_fv fv2 Hlt_c_fv_e1_fv Hlt_e1_fv_fv2). }
    apply (lt_trans fv1 c_fv fv2 Hlt_fv1_c_fv Hlt_c_fv_fv2).
  - assert (Hlt_fv1_t: fv1 < max_typevar t fv1 + 1).
      { apply (max_typevar_larger_fv t fv1). }
    assert (Hlt_t_fv2: max_typevar t fv1 + 1< fv2).
      { apply (IHe (update t_env i t) (max_typevar t fv1 + 1) fv2 e_T C X Htie1). }
    apply (lt_trans fv1 (max_typevar t fv1 + 1) fv2 Hlt_fv1_t Hlt_t_fv2).
  - assert (Hlt_fv1_f_fv: fv1 < f_fv).
      { apply (IHe1 t_env fv1 f_fv f_T f_C f_X Htie1). }
    assert (Hlt_f_fv_e_fv: f_fv < e_fv).
      { apply (IHe2 t_env f_fv e_fv e_T e_C e_X Htie2). }
    assert (Hlt_fv1_e_fv: fv1 < e_fv).
      { apply (lt_trans fv1 f_fv e_fv Hlt_fv1_f_fv Hlt_f_fv_e_fv). }
    apply (lt_trans fv1 e_fv (e_fv + 1) Hlt_fv1_e_fv (lt_n_n_1 e_fv)).
  - assert (Hlt_fv1_e1_fv: fv1 < e1_fv).
      { apply (IHe1 t_env fv1 e1_fv e1_T e1_C e1_X Htie1). }
    assert (Hlt_e1_fv_fv2: e1_fv < fv2).
      { apply (IHe2 t_env e1_fv fv2 e2_T e2_C e2_X Htie2). }
    apply (lt_trans fv1 e1_fv fv2 Hlt_fv1_e1_fv Hlt_e1_fv_fv2).
  - assert (Hlt_fv1_e1_fv: fv1 < e1_fv).
      { apply (IHe1 t_env fv1 e1_fv e1_T e1_C e1_X Htie1). }
    assert (Hlt_e1_fv_fv2: e1_fv < fv2).
      { apply (IHe2 t_env e1_fv fv2 e2_T e2_C e2_X Htie2). }
    apply (lt_trans fv1 e1_fv fv2 Hlt_fv1_e1_fv Hlt_e1_fv_fv2).
  - assert (Hlt_fv1_e1_fv: fv1 < e1_fv).
      { apply (IHe1 t_env fv1 e1_fv e1_T e1_C e1_X Htie1). }
    assert (Hlt_e1_fv_fv2: e1_fv < fv2).
      { apply (IHe2 t_env e1_fv fv2 e2_T e2_C e2_X Htie2). }
    apply (lt_trans fv1 e1_fv fv2 Hlt_fv1_e1_fv Hlt_e1_fv_fv2).
  - assert (Hlt_fv1_hd_fv: fv1 < hd_fv).
      { apply (IHe1 t_env fv1 hd_fv hd_T hd_C hd_X Htie1). }
    assert (Hlt_hd_fv_fv2: hd_fv < fv2).
      { apply (IHe2 t_env hd_fv fv2 tl_T tl_C tl_X Htie2). }
    apply (lt_trans fv1 hd_fv fv2 Hlt_fv1_hd_fv Hlt_hd_fv_fv2).
  - apply (max_typevar_larger_fv t fv1).
Qed.

Lemma typeinf_X_between_fvs :
  forall e t_env fv1 fv2 S C X,
    typeinf t_env fv1 e (fv2, S, C, X) ->
    (forall n, In (Id n) X -> fv1 < n /\ n < fv2).
Proof.
  induction e;
  introv Hti;
  inverts Hti as Htie1 Htie2 Htie3;
  introv Hin;
  try (inverts Hin);
  sort.

  (* EIf *)
  - apply in_app_or in Hin. destruct Hin as [Hine2X|Hine1cX].
    * assert (Hlt_e1_fv_n_fv2: e1_fv < n < fv2).
        { apply ((IHe3 t_env e1_fv fv2 e2_T e2_C e2_X Htie3) n Hine2X). }
      destruct Hlt_e1_fv_n_fv2 as [Hlt_e1_fv_n Hlt_n_fv2].
      assert (Hlt_fv1_c_fv: fv1 < c_fv).
        { apply (typeinf_larger_fv e1 t_env fv1 c_fv c_T c_C c_X Htie1). }
      assert (Hlt_c_fv_e1_fv: c_fv < e1_fv).
        { apply (typeinf_larger_fv e2 t_env c_fv e1_fv S e1_C e1_X Htie2). }
      assert (Hlt_fv1_e1_fv: fv1 < e1_fv).
        { apply (lt_trans fv1 c_fv e1_fv Hlt_fv1_c_fv Hlt_c_fv_e1_fv). }
      assert (Hlt_fv1_n: fv1 < n).
        { apply (lt_trans fv1 e1_fv n Hlt_fv1_e1_fv Hlt_e1_fv_n). }
      split; assumption.
    * apply in_app_or in Hine1cX. destruct Hine1cX as [Hine1X|HincX].
      + assert (Hlt_c_fv_n_e1_fv: c_fv < n < e1_fv).
          { apply ((IHe2 t_env c_fv e1_fv S e1_C e1_X Htie2) n Hine1X). }
        destruct Hlt_c_fv_n_e1_fv as [Hlt_c_fv_n Hlt_n_e1_fv].
        assert (Hlt_fv1_c_fv: fv1 < c_fv).
          { apply (typeinf_larger_fv e1 t_env fv1 c_fv c_T c_C c_X Htie1). }
        assert (Hlt_e1_fv_fv2: e1_fv < fv2).
          { apply (typeinf_larger_fv e3 t_env e1_fv fv2 e2_T e2_C e2_X Htie3). }
        assert (Hlt_fv1_n: fv1 < n).
          { apply (lt_trans fv1 c_fv n Hlt_fv1_c_fv Hlt_c_fv_n). }
        assert (Hlt_n_fv2: n < fv2).
          { apply (lt_trans n e1_fv fv2 Hlt_n_e1_fv Hlt_e1_fv_fv2). }
        split; assumption.
      + assert (Hlt_fv1_n_c_fv: fv1 < n < c_fv).
          { apply ((IHe1 t_env fv1 c_fv c_T c_C c_X Htie1) n HincX). }
        destruct Hlt_fv1_n_c_fv as [Hlt_fv1_n Hlt_n_c_fv].
        assert (Hlt_c_fv_e1_fv: c_fv < e1_fv).
          { apply (typeinf_larger_fv e2 t_env c_fv e1_fv S e1_C e1_X Htie2). }
        assert (Hlt_e1_fv_fv2: e1_fv < fv2).
          { apply (typeinf_larger_fv e3 t_env e1_fv fv2 e2_T e2_C e2_X Htie3). }
        assert (Hlt_c_fv_fv2: c_fv < fv2).
          { apply (lt_trans c_fv e1_fv fv2 Hlt_c_fv_e1_fv Hlt_e1_fv_fv2). }
        assert (Hlt_n_fv2: n < fv2).
          { apply (lt_trans n c_fv fv2 Hlt_n_c_fv Hlt_c_fv_fv2). }
        split; assumption.

  (* EFun *)
  - assert (Hlt_t_fv2: (max_typevar t fv1 + 1) < n < fv2).
      { apply ((IHe (update t_env i t) (max_typevar t fv1 + 1) fv2 e_T C X Htie1) n Hin). }
    destruct Hlt_t_fv2 as [Hlt_t_n Hlt_n_fv2].
    assert (Hlt_fv1_t: fv1 < max_typevar t fv1 + 1).
      { apply (max_typevar_larger_fv t fv1). }
    assert (Hlt_fv1_n: fv1 < n).
      { apply (lt_trans fv1 (max_typevar t fv1 + 1) n Hlt_fv1_t Hlt_t_n). }
    split; assumption.

  (* ECall *)
  - apply in_app_or in Hin. destruct Hin as [HineX|HinfXefv].
    * assert (Hlt_f_fv_n_e_fv: f_fv < n < e_fv).
        { apply ((IHe2 t_env f_fv e_fv e_T e_C e_X Htie2) n HineX). }
      destruct Hlt_f_fv_n_e_fv as [Hlt_f_fv_n Hlt_n_e_fv].
      assert (Hlt_fv1_f_fv: fv1 < f_fv).
        { apply (typeinf_larger_fv e1 t_env fv1 f_fv f_T f_C f_X Htie1). }
      assert (Hlt_fv1_n: fv1 < n).
        { apply (lt_trans fv1 f_fv n Hlt_fv1_f_fv Hlt_f_fv_n). }
      assert (Hlt_n_e_fv_1: n < e_fv + 1).
        { apply (lt_trans n e_fv (e_fv + 1) Hlt_n_e_fv (lt_n_n_1 e_fv)). }
      split; assumption.
    * apply in_app_or in HinfXefv. destruct HinfXefv as [HinfX|Hinefv].
      + assert (Hlt_fv1_n_f_fv: fv1 < n < f_fv).
          { apply ((IHe1 t_env fv1 f_fv f_T f_C f_X Htie1) n HinfX). }
        destruct Hlt_fv1_n_f_fv as [Hlt_fv1_n Hlt_n_f_fv].
        assert (Hlt_f_fv_e_fv: f_fv < e_fv).
          { apply (typeinf_larger_fv e2 t_env f_fv e_fv e_T e_C e_X Htie2). }
        assert (Hlt_n_e_fv: n < e_fv).
          { apply (lt_trans n f_fv e_fv Hlt_n_f_fv Hlt_f_fv_e_fv). }
        assert (Hlt_n_e_fv_1: n < e_fv + 1).
          { apply (lt_trans n e_fv (e_fv + 1) Hlt_n_e_fv (lt_n_n_1 e_fv)). }
        split; assumption.
      + simpl in Hinefv. destruct Hinefv as [Hefvn|Hfalse].
        { assert (Hlt_fv1_f_fv: fv1 < f_fv).
            { apply (typeinf_larger_fv e1 t_env fv1 f_fv f_T f_C f_X Htie1). }
          assert (Hlt_f_fv_e_fv: f_fv < e_fv).
            { apply (typeinf_larger_fv e2 t_env f_fv e_fv e_T e_C e_X Htie2). }
          inverts Hefvn.
          assert (Hlt_fv1_n: fv1 < n).
            { apply (lt_trans fv1 f_fv n Hlt_fv1_f_fv Hlt_f_fv_e_fv). }
          assert (Hlt_n_n_1: n < n + 1).
            { apply (lt_n_n_1 n). }
          split; assumption. }
        { inverts Hfalse. }

  (* EBinop *)
  - apply in_app_or in Hin. destruct Hin as [Hine2X|Hine1X].
    * assert (Hlt_e1_fv_n_fv2: e1_fv < n < fv2).
        { apply ((IHe2 t_env e1_fv fv2 e2_T e2_C e2_X Htie2) n Hine2X). }
      destruct Hlt_e1_fv_n_fv2 as [Hlt_e1_fv_n Hlt_n_fv2].
      assert (Hlt_fv1_e1_fv: fv1 < e1_fv).
        { apply (typeinf_larger_fv e1 t_env fv1 e1_fv e1_T e1_C e1_X Htie1). }
      assert (Hlt_fv1_n: fv1 < n).
        { apply (lt_trans fv1 e1_fv n Hlt_fv1_e1_fv Hlt_e1_fv_n). }
      split; assumption.
    * assert (Hlt_fv1_n_e1_fv: fv1 < n < e1_fv).
        { apply ((IHe1 t_env fv1 e1_fv e1_T e1_C e1_X Htie1) n Hine1X). }
      destruct Hlt_fv1_n_e1_fv as [Hlt_fv1_n Hlt_n_e1_fv].
      assert (Hlt_e1_fv_fv2: e1_fv < fv2).
        { apply (typeinf_larger_fv e2 t_env e1_fv fv2 e2_T e2_C e2_X Htie2). }
      assert (Hlt_n_fv2: n < fv2).
        { apply (lt_trans n e1_fv fv2 Hlt_n_e1_fv Hlt_e1_fv_fv2). }
      split; assumption.

  - apply in_app_or in Hin. destruct Hin as [Hine2X|Hine1X].
    * assert (Hlt_e1_fv_n_fv2: e1_fv < n < fv2).
        { apply ((IHe2 t_env e1_fv fv2 e2_T e2_C e2_X Htie2) n Hine2X). }
      destruct Hlt_e1_fv_n_fv2 as [Hlt_e1_fv_n Hlt_n_fv2].
      assert (Hlt_fv1_e1_fv: fv1 < e1_fv).
        { apply (typeinf_larger_fv e1 t_env fv1 e1_fv e1_T e1_C e1_X Htie1). }
      assert (Hlt_fv1_n: fv1 < n).
        { apply (lt_trans fv1 e1_fv n Hlt_fv1_e1_fv Hlt_e1_fv_n). }
      split; assumption.
    * assert (Hlt_fv1_n_e1_fv: fv1 < n < e1_fv).
        { apply ((IHe1 t_env fv1 e1_fv e1_T e1_C e1_X Htie1) n Hine1X). }
      destruct Hlt_fv1_n_e1_fv as [Hlt_fv1_n Hlt_n_e1_fv].
      assert (Hlt_e1_fv_fv2: e1_fv < fv2).
        { apply (typeinf_larger_fv e2 t_env e1_fv fv2 e2_T e2_C e2_X Htie2). }
      assert (Hlt_n_fv2: n < fv2).
        { apply (lt_trans n e1_fv fv2 Hlt_n_e1_fv Hlt_e1_fv_fv2). }
      split; assumption.

  - apply in_app_or in Hin. destruct Hin as [Hine2X|Hine1X].
    * assert (Hlt_e1_fv_n_fv2: e1_fv < n < fv2).
        { apply ((IHe2 t_env e1_fv fv2 e2_T e2_C e2_X Htie2) n Hine2X). }
      destruct Hlt_e1_fv_n_fv2 as [Hlt_e1_fv_n Hlt_n_fv2].
      assert (Hlt_fv1_e1_fv: fv1 < e1_fv).
        { apply (typeinf_larger_fv e1 t_env fv1 e1_fv e1_T e1_C e1_X Htie1). }
      assert (Hlt_fv1_n: fv1 < n).
        { apply (lt_trans fv1 e1_fv n Hlt_fv1_e1_fv Hlt_e1_fv_n). }
      split; assumption.
    * assert (Hlt_fv1_n_e1_fv: fv1 < n < e1_fv).
        { apply ((IHe1 t_env fv1 e1_fv e1_T e1_C e1_X Htie1) n Hine1X). }
      destruct Hlt_fv1_n_e1_fv as [Hlt_fv1_n Hlt_n_e1_fv].
      assert (Hlt_e1_fv_fv2: e1_fv < fv2).
        { apply (typeinf_larger_fv e2 t_env e1_fv fv2 e2_T e2_C e2_X Htie2). }
      assert (Hlt_n_fv2: n < fv2).
        { apply (lt_trans n e1_fv fv2 Hlt_n_e1_fv Hlt_e1_fv_fv2). }
      split; assumption.

  (* ECons *)
  - apply in_app_or in Hin. destruct Hin as [HintlX|HinhdX].
    * assert (Hlt_hd_fv_n_fv2: hd_fv < n < fv2).
        { apply ((IHe2 t_env hd_fv fv2 tl_T tl_C tl_X Htie2) n HintlX). }
      destruct Hlt_hd_fv_n_fv2 as [Hlt_hd_fv_n Hlt_n_fv2].
      assert (Hlt_fv1_hd_fv: fv1 < hd_fv).
        { apply (typeinf_larger_fv e1 t_env fv1 hd_fv hd_T hd_C hd_X Htie1). }
      assert (Hlt_fv1_n: fv1 < n).
        { apply (lt_trans fv1 hd_fv n Hlt_fv1_hd_fv Hlt_hd_fv_n). }
      split; assumption.
    * assert (Hlt_fv1_n_hd_fv: fv1 < n < hd_fv).
        { apply ((IHe1 t_env fv1 hd_fv hd_T hd_C hd_X Htie1) n HinhdX). }
      destruct Hlt_fv1_n_hd_fv as [Hlt_fv1_n Hlt_n_hd_fv].
      assert (Hlt_hd_fv_fv2: hd_fv < fv2).
        { apply (typeinf_larger_fv e2 t_env hd_fv fv2 tl_T tl_C tl_X Htie2). }
      assert (Hlt_n_fv2: n < fv2).
        { apply (lt_trans n hd_fv fv2 Hlt_n_hd_fv Hlt_hd_fv_fv2). }
      split; assumption.
Qed.

Lemma typeinf_disjoint_Xs :
  forall
    t_env1 e1 S1 C1 X1
    t_env2 e2 S2 C2 X2
    fv1 fv2 fv3,
  typeinf t_env1 fv1 e1 (fv2, S1, C1, X1) ->
  typeinf t_env2 fv2 e2 (fv3, S2, C2, X2) ->
  (forall x, ~ (In x X1 /\ In x X2)).
Proof.
  introv Htie1 Htie2.
  introv.
  introv Hand.
  destruct Hand as [HxX1 HxX2].
  destruct x.
  assert (Hlt_fv1_n_fv2: fv1 < n < fv2).
    { apply ((typeinf_X_between_fvs e1 t_env1 fv1 fv2 S1 C1 X1 Htie1) n HxX1). }
  assert (Hlt_fv2_n_fv3: fv2 < n < fv3).
    { apply ((typeinf_X_between_fvs e2 t_env2 fv2 fv3 S2 C2 X2 Htie2) n HxX2). }
  destruct Hlt_fv1_n_fv2 as [Hlt_fv1_n Hlt_n_fv2].
  destruct Hlt_fv2_n_fv3 as [Hlt_fv2_n Hlt_n_fv3].
  apply (lt_n_n n (lt_trans n fv2 n Hlt_n_fv2 Hlt_fv2_n)).
Qed.

Lemma app_sub_type_omit_disjoint_list :
  forall T sub l,
    (forall i, ~(In i (typevars T) /\ In i l)) ->
    app_sub_to_type (omit sub l) T = app_sub_to_type sub T.
Proof.
  induction T;
  introv Hnin;
  simpl in Hnin;
  simpl;
  unfold not in Hnin;
  try reflexivity.
  - assert (HT1: forall i : id, ~ (In i (typevars T1) /\ In i l)).
      { introv. unfold not.
        introv Hini. destruct Hini.
        apply (Hnin i). split.
        - apply in_or_app. left. assumption.
        - assumption. }
    assert (HT2: forall i : id, ~ (In i (typevars T2) /\ In i l)).
      { introv. unfold not.
        introv Hini. destruct Hini.
        apply (Hnin i). split.
        - apply in_or_app. right. assumption.
        - assumption. }
    rewrite (IHT1 sub l HT1).
    rewrite (IHT2 sub l HT2).
    reflexivity.
  - rewrite (IHT sub l Hnin).
    reflexivity.
  - assert (Hini: ~ (In i l)).
    { unfold not. introv Hin.
      apply (Hnin i). split.
      - left. reflexivity.
      - assumption. }
    rewrite (omit_not_in_list t_type l i sub Hini).
    reflexivity.
Qed.
