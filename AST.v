Require Import String.
Require Import List.

Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Require Import Maps.

Inductive type : Type :=
  | TNum : type
  | TBool : type
  | TFun : type -> type -> type
  | TList : type -> type
  | TVar : id -> type. (* use number to easily generate type variables *)

Inductive binop : Type :=
  | op_Plus : binop
  | op_Minus : binop
  | op_Mult : binop
  | op_Div : binop
  | op_Mod : binop
  | op_Eq : binop
  | op_Neq : binop
  | op_Lt : binop
  | op_Gt : binop
  | op_And : binop
  | op_Or : binop.

Inductive ut_expr : Type := (* ut_expr : untyped expression *)
  | ut_Num : nat -> ut_expr
  | ut_Bool : bool -> ut_expr
  | ut_Var : id -> ut_expr
  | ut_If : ut_expr -> ut_expr -> ut_expr -> ut_expr
  | ut_Fun : id -> ut_expr -> ut_expr
  | ut_Call : ut_expr -> ut_expr -> ut_expr
  | ut_Binop : binop -> ut_expr -> ut_expr -> ut_expr
  | ut_Cons : ut_expr -> ut_expr -> ut_expr
  | ut_Nil : ut_expr.

Inductive t_expr : Type := (* t_expr : typed expression *)
  | t_Num : nat -> t_expr
  | t_Bool : bool -> t_expr
  | t_Var : id -> t_expr
  | t_If : t_expr -> t_expr -> t_expr -> t_expr
  | t_Fun : id -> type -> t_expr -> t_expr
  | t_Call : t_expr -> t_expr -> t_expr
  | t_Binop : binop -> t_expr -> t_expr -> t_expr
  | t_Cons : t_expr -> t_expr -> t_expr
  | t_Nil : type -> t_expr.

Definition environment := partial_map type.
Definition constraint := list (type * type) % type.
Definition substitution := list (id * type) % type.

Fixpoint erase (t_ex : t_expr) : ut_expr :=
  match t_ex with
    | t_Num n => ut_Num n
    | t_Bool b => ut_Bool b
    | t_Var x => ut_Var x
    | t_If c e1 e2 => ut_If (erase c) (erase e1) (erase e2)
    | t_Fun x t e => ut_Fun x (erase e)
    | t_Call f e => ut_Call (erase f) (erase e)
    | t_Binop op e1 e2 => ut_Binop op (erase e1) (erase e2)
    | t_Cons hd tl => ut_Cons (erase hd) (erase tl)
    | t_Nil t => ut_Nil
  end.
