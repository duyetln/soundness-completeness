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
  | TDatum : id string -> list type -> type
  | TDelayed : type -> type
  | TAny : type
  | TVar : id string -> type
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

Inductive pattern : Type :=
  | PNum : nat -> pattern
  | PBool : bool -> pattern
  | PVar : id string -> pattern
  | PDatum : id string -> list pattern -> pattern.

Inductive expr : Type :=
  | TmNum : nat -> expr
  | TmBool : bool -> expr
  | TmVar : id string -> expr
  | TmIf : expr -> expr -> expr -> expr
  | TmNFun : expr -> expr
  | TmUFun : id string -> option type -> expr -> expr
  | TmCall : expr -> expr -> expr
  | TmLet : id string -> expr -> expr -> expr
  | TmBinop : binop -> expr -> expr -> expr
  | TmDatum : id string -> list expr -> expr
  | TmMatch : expr -> list pattern -> list expr -> expr
  | TmCons : expr -> expr
  | TmNil : expr
  | TmListComp : list expr -> id string -> expr -> expr
  | TmDelay : expr -> expr
  | TmForce : expr -> expr.

Example expr1 := TmNum 1.
Example expr2 := TmBool true.
Example expr3 := (TmUFun "x" None (TmBinop OpPlus (TmVar "x") (TmNum 1))).
Example expr4 := (TmCall expr3 expr1).
Example expr5 := (TmLet "x" expr4 (TmVar "x")).
Example expr6 := (TmDatum "C" [TmNum 1; TmNum 2]).
Example expr7 := (TmMatch (TmNum 1) [PNum 1; PNum 2] [TmNum 1; TmNum 2]).
Example expr8 := (TmListComp [TmNum 1; TmNum 2] "x" expr3).


