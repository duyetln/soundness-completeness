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
  | TDelay : type -> type
  | TVar : nat -> type (* use number to easily generate type variables *)
  | TUnit : type.

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
  | TmNFun : expr -> expr
  | TmUFun : string -> option type -> expr -> expr
  | TmCall : expr -> expr -> expr
  | TmLet : string -> expr -> expr -> expr
  | TmBinop : binop -> expr -> expr -> expr
  | TmCons : expr -> expr -> expr
  | TmNil : expr
  | TmDelay : expr -> expr
  | TmForce : expr -> expr.

Example expr1 := TmNum 1.
Example expr2 := TmBool true.
Example expr3 := (TmUFun "x" None (TmBinop OpPlus (TmVar "x") (TmNum 1))).
Example expr4 := (TmCall expr3 expr1).
Example expr5 := (TmLet "x" expr4 (TmVar "x")).
