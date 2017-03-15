(* Maps: Total and Partial Maps *)
(* Copied from SF's Maps.v *)
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import List.
Import ListNotations.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. rewrite <- beq_nat_refl.
  reflexivity. Qed.

Theorem beq_id_true_iff : forall id1 id2 : id,
  beq_id id1 id2 = true <-> id1 = id2.
Proof.
   intros [n1] [n2].
   unfold beq_id.
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H. Qed.

Lemma id_dec :
  forall x x' : id, { x = x' } + { x <> x' }.
Proof.
  repeat (decide equality).
Qed.

(* Total maps *)

Definition total_map (A:Type) := id -> A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true.

Example update_example1 : examplemap (Id 0) = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap (Id 1) = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap (Id 2) = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap (Id 3) = true.
Proof. reflexivity. Qed.

Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
Proof.
  reflexivity.
Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros A m x v.
  unfold t_update.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  intros X v x1 x2 m H.
  apply false_beq_id in H.
  unfold t_update.
  rewrite H.
  reflexivity.
Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros A m v1 v2 x.
  unfold t_update.
  apply functional_extensionality_dep. intros x'.
  destruct (beq_id x x') eqn:H.
  - reflexivity.
  - reflexivity.
Qed.

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply beq_id_true_iff.
Qed.

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  intros X x m.
  unfold t_update.
  apply functional_extensionality_dep. intros x0.
  destruct (beq_id x x0) eqn:H.
  - apply beq_id_true_iff in H. rewrite H. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m H.
  unfold t_update.
  apply functional_extensionality_dep. intros x0.
  destruct (beq_id x1 x0) eqn:H1.
  - destruct (beq_id x2 x0) eqn:H2.
    * apply beq_id_true_iff in H1. rewrite H1 in H.
      apply beq_id_true_iff in H2. rewrite H2 in H.

      (*
      unfold not in H.
      exfalso.
      apply H.
      *)
      destruct H.
      reflexivity.
    * reflexivity.
  - destruct (beq_id x2 x0) eqn:H2.
    * reflexivity.
    * reflexivity.
Qed.

(* Partial maps *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A) (x : id) (v : A) :=
  t_update m x (Some v).

Definition key {A:Type} (m : partial_map A) (x : id) : bool :=
  match m x with
    | Some _ => true
    | None => false
  end.

Definition remove {A:Type} (m : partial_map A) (x : id) : partial_map A :=
  if key m x then t_update m x None else m.

Definition merge {A:Type} (m1 m2 : partial_map A) : partial_map A :=
  fun i => if key m2 i then m2 i else m1 i.

Fixpoint omit {A:Type} (m : partial_map A) (l : list id) : partial_map A :=
  match l with
    | [] => m
    | i::l' => omit (remove m i) l'
  end.


(** We can now lift all of the basic lemmas about total maps to
    partial maps.  *)

Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H.
Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.

Theorem key_true_iff : forall X (m : partial_map X) x,
  key m x = true <-> (exists x', m x = Some x').
Proof.
  intros X m x. split.
  - intros H.
    unfold key in H.
    destruct (m x) eqn:Hmx.
    * exists x0. reflexivity.
    * inversion H.
  - intros H.
    destruct H.
    unfold key.
    rewrite H.
    reflexivity.
Qed.

Theorem key_false_iff : forall X (m : partial_map X) x,
  key m x = false <-> m x = None.
Proof.
  intros X m x. split.
  - intros.
    unfold key in H.
    destruct (m x) eqn:Hmx.
    * inversion H.
    * reflexivity.
  - intros H.
    unfold key.
    rewrite H.
    reflexivity.
Qed.

Lemma remove_eq : forall A (m: partial_map A) x,
  (remove m x) x = None.
Proof.
  intros. unfold remove.
  destruct (key m x) eqn:Hmx.
  - apply t_update_eq.
  - apply key_false_iff. assumption.
Qed.

Theorem remove_neq : forall X (m : partial_map X) x1 x2,
  x2 <> x1 -> (remove m x2) x1 = m x1.
Proof.
  intros X m x1 x2 H.
  unfold remove.
  destruct (key m x2) eqn:Hmx2.
  - apply t_update_neq. assumption.
  - reflexivity.
Qed.

Theorem merge_shadow_key : forall A (m1 m2: partial_map A) x,
  key m2 x = true ->
  merge m1 m2 x = m2 x.
Proof.
  intros A m1 m2 x H.
  unfold merge.
  rewrite H.
  reflexivity.
Qed.

Theorem merge_shadow_not_key : forall A (m1 m2: partial_map A) x,
  key m2 x = false ->
  merge m1 m2 x = m1 x.
Proof.
  intros A m1 m2 x H.
  unfold merge.
  rewrite H.
  reflexivity.
Qed.

Lemma omit_none :
  forall A l i (m : partial_map A), m i = None -> (omit m l) i = None.
Proof.
  intros A.
  induction l as [|i' l'];
  intros i m Hmi;
  simpl.
  - assumption.
  - destruct (id_dec i' i) as [Heq|Hneq].
    * apply (IHl' i (remove m i')).
      rewrite Heq. apply remove_eq.
    * apply (IHl' i (remove m i')).
      rewrite <- Hmi. apply remove_neq.
      assumption.
Qed.

Lemma omit_not_in_list :
  forall A l i (m : partial_map A),
    not (In i l) -> (omit m l) i = m i.
Proof.
  intros A.
  induction l as [|i' l'];
  intros i m Hli;
  simpl.
  - reflexivity.
  - destruct (id_dec i' i) as [Heq|Hneq].
    * exfalso. apply Hli. simpl. left. assumption.
    * rewrite (IHl' i (remove m i')).
      + apply remove_neq. assumption.
      + intro. apply Hli. simpl. right. assumption.
Qed.

Lemma omit_in_list :
  forall A l i (m : partial_map A),
    In i l ->
    (omit m l) i = None.
Proof.
  intros A.
  induction l as [|i' l'];
  intros i m Hli;
  inversion Hli;
  simpl.
  - rewrite H. apply (omit_none A l' i (remove m i)). apply remove_eq.
  - apply (IHl' i (remove m i') H).
Qed.

Theorem omit_list_iff :
  forall A (m : partial_map A) l,
    (forall i, In i l -> m i = None) <-> omit m l = m.
Proof.
  intros. split.
  - intros Hmi. apply functional_extensionality_dep. intros.
    destruct (in_dec id_dec x l) as [Hxl|Hnxl].
    * rewrite (omit_in_list A l x m Hxl), (Hmi x Hxl). reflexivity.
    * rewrite (omit_not_in_list A l x m Hnxl). reflexivity.
  - intros Hml. intros x Hil.
    rewrite <- (omit_in_list A l x m Hil), Hml. reflexivity.
Qed.
