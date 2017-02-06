Require Import String.
Require Import List.

Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.


Inductive type : Type :=
  | TNum : type
  | TBool : type
  | TFun : type -> type -> type
  | TList : type -> type
  | TVar : nat -> type. (* use number to easily generate type variables *)

Inductive binop : Type :=
  | OpPlus : binop
  | OpMinus : binop
  | OpMult : binop
  | OpDiv : binop
  | OpMod : binop
  | OpEq : binop
  | OpNeq : binop
  | OpLt : binop
  | OpGt : binop
  | OpAnd : binop
  | OpOr : binop.

Inductive expr : Type :=
  | TmNum : nat -> expr
  | TmBool : bool -> expr
  | TmVar : string -> expr
  | TmIf : expr -> expr -> expr -> expr
  | TmFun : string -> option type -> expr -> expr
  | TmCall : expr -> expr -> expr
  | TmBinop : binop -> expr -> expr -> expr
  | TmCons : expr -> expr -> expr
  | TmNil : expr.

Example expr1 := TmNum 1.
Example expr2 := TmBool true.
Example expr3 := (TmFun "x" None (TmBinop OpPlus (TmVar "x") (TmNum 1))).
Example expr4 := (TmCall expr3 expr1).
