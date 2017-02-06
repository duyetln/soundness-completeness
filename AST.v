Require Import String.
Require Import List.

Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Require Import Util.

Inductive type : Type :=
  | TNum : type
  | TBool : type
  | TFun : type -> type -> type
  | TList : type -> type
  | TVar : nat -> type. (* use number to easily generate type variables *)

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
  | ut_Var : string -> ut_expr
  | ut_If : ut_expr -> ut_expr -> ut_expr -> ut_expr
  | ut_Fun : string -> ut_expr -> ut_expr
  | ut_Call : ut_expr -> ut_expr -> ut_expr
  | ut_Binop : binop -> ut_expr -> ut_expr -> ut_expr
  | ut_Cons : ut_expr -> ut_expr -> ut_expr
  | ut_Nil : ut_expr.

Inductive t_expr : Type := (* t_expr : typed expression *)
  | t_Num : nat -> t_expr
  | t_Bool : bool -> t_expr
  | t_Var : string -> t_expr
  | t_If : t_expr -> t_expr -> t_expr -> t_expr
  | t_Fun : string -> type -> t_expr -> t_expr
  | t_Call : t_expr -> t_expr -> t_expr
  | t_Binop : binop -> t_expr -> t_expr -> t_expr
  | t_Cons : t_expr -> t_expr -> t_expr
  | t_Nil : type -> t_expr.

Definition environment := (@dict string type) % type.

Definition type_from_env (x : string) (env : environment) : option type :=
  dict_get x str_eqb env.
