Require Import String.
Require Import Ascii.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Definition str_len := String.length.
Definition list_len := List.length.

Fixpoint str_eqb (a b : string) : bool :=
  match a, b with
    | EmptyString, EmptyString => true
    | String ac arest, String bc brest =>
      if eqb (nat_of_ascii ac) (nat_of_ascii bc) then str_eqb arest brest
      else false
    | _, _ => false
  end.

Definition dict { K V : Type } := list (K * V) % type.
Fixpoint dict_get { K V : Type } (k : K) (eq : K -> K -> bool) (d : @dict K V) : option V :=
  match d with
    | [] => None
    | (k1, v1)::t => if eq k k1 then Some v1 else dict_get k eq t
  end.

Example ex1 : dict_get 1 eqb [(1, "value")] = Some "value".
Proof.
  simpl. reflexivity.
Qed.

Fixpoint dict_in { K V : Type } (k : K) (eq : K -> K -> bool) (d : @dict K V) : bool :=
  match dict_get k eq d with
    | None => false
    | Some _ => true
  end.

Example ex2 : dict_in "key" str_eqb [("key", 1)] = true.
Proof.
  simpl. reflexivity.
Qed.

Fixpoint dict_remove { K V : Type } (k : K) (eq : K -> K -> bool) (d : @dict K V) : (@dict K V) :=
  match d with
    | [] => []
    | (k1, v1)::t => if eq k k1 then t else (k1, v1)::(dict_remove k eq t)
  end.

Example ex3 : dict_in "key" str_eqb (dict_remove "key" str_eqb [("key", 1)]) = false.
Proof.
  simpl. reflexivity.
Qed.

Definition dict_insert { K V : Type } ( p : (K * V) % type) (eq : K -> K -> bool) (d : @dict K V) : (@dict K V) :=
  let (k, v) := p in
    if dict_in k eq d then p::(dict_remove k eq d)
    else p::d.
Example ex4 : dict_get "key" str_eqb (dict_insert ("key", "value") str_eqb [("key", "foo")]) = Some "value".
Proof.
  simpl. reflexivity.
Qed.

