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
