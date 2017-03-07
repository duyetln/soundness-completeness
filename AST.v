Require Import String.
Require Import List.

Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Require Import Maps.

Inductive t_type : Type :=
  | TNum: t_type
  | TBool: t_type
  | TFun: t_type -> t_type -> t_type
  | TList: t_type -> t_type
  | TVar: id -> t_type. (* id from Maps.v *)

Inductive binop : Type :=
  | OpPlus: binop
  | OpMinus: binop
  | OpEq: binop
  | OpNeq: binop
  | OpAnd: binop
  | OpOr: binop.

Inductive t_expr : Type := (* t_expr : typed expression *)
  | ENum: nat -> t_expr
  | EBool: bool -> t_expr
  | EVar: id -> t_expr
  | EIf: t_expr -> t_expr -> t_expr -> t_expr
  | EFun: id -> t_type -> t_expr -> t_expr
  | ECall: t_expr -> t_expr -> t_expr
  | EBinop: binop -> t_expr -> t_expr -> t_expr
  | ECons: t_expr -> t_expr -> t_expr
  | ENil: t_type -> t_expr.

Definition t_env := partial_map t_type.
Definition constr := list (t_type * t_type) % type.
Definition substs := partial_map t_type.

Definition empty_t_env := @empty t_type.
Definition empty_constr := @nil (t_type * t_type) % type.
Definition empty_substs := @empty t_type.

Inductive concrete_type : t_type -> Prop :=
  | CT_Num: concrete_type TNum
  | CT_Bool: concrete_type TBool
  | CT_Fun:
    forall x e,
    concrete_type x ->
    concrete_type e ->
    concrete_type (TFun x e)
  | CT_List:
    forall l,
    concrete_type l  ->
    concrete_type (TList l).
