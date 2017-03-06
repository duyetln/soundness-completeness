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
  | op_Plus: binop
  | op_Minus: binop
  | op_Eq: binop
  | op_Neq: binop
  | op_And: binop
  | op_Or: binop.

Inductive ut_expr : Type := (* ut_expr : untyped expression *)
  | ut_Num: nat -> ut_expr
  | ut_Bool: bool -> ut_expr
  | ut_Var: id -> ut_expr
  | ut_If: ut_expr -> ut_expr -> ut_expr -> ut_expr
  | ut_Fun: id -> ut_expr -> ut_expr
  | ut_Call: ut_expr -> ut_expr -> ut_expr
  | ut_Binop: binop -> ut_expr -> ut_expr -> ut_expr
  | ut_Cons: ut_expr -> ut_expr -> ut_expr
  | ut_Nil: ut_expr.

Inductive t_expr : Type := (* t_expr : typed expression *)
  | t_Num: nat -> t_expr
  | t_Bool: bool -> t_expr
  | t_Var: id -> t_expr
  | t_If: t_expr -> t_expr -> t_expr -> t_expr
  | t_Fun: id -> t_type -> t_expr -> t_expr
  | t_Call: t_expr -> t_expr -> t_expr
  | t_Binop: binop -> t_expr -> t_expr -> t_expr
  | t_Cons: t_expr -> t_expr -> t_expr
  | t_Nil: t_type -> t_expr.

Definition t_env := partial_map t_type.
Definition constr := list (t_type * t_type) % type.
Definition substs := list (id * t_type) % type.

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

Inductive convert_expr : t_expr -> ut_expr -> Prop :=
  | CE_Num: forall n, convert_expr (t_Num n) (ut_Num n)
  | CE_Bool: forall b, convert_expr (t_Bool b) (ut_Bool b)
  | CE_Var: forall x, convert_expr (t_Var x) (ut_Var x)
  | CE_If: forall c c_e e1 e1_e e2 e2_e,
    convert_expr c c_e ->
    convert_expr e1 e1_e ->
    convert_expr e2 e2_e ->
    convert_expr (t_If c e1 e2) (ut_If c_e e1_e e2_e)
  | CE_Fun: forall x t e e_e,
    convert_expr e e_e ->
    convert_expr (t_Fun x t e) (ut_Fun x e_e)
  | CE_Call: forall f f_e e e_e,
    convert_expr f f_e ->
    convert_expr e e_e ->
    convert_expr (t_Call f e) (ut_Call f_e e_e)
  | CE_Binop: forall op e1 e1_e e2 e2_e,
    convert_expr e1 e1_e ->
    convert_expr e2 e2_e ->
    convert_expr (t_Binop op e1 e2) (ut_Binop op e1_e e2_e)
  | CE_Cons: forall hd hd_e tl tl_e,
    convert_expr hd hd_e ->
    convert_expr tl tl_e ->
    convert_expr (t_Cons hd tl) (ut_Cons hd_e tl_e)
  | CE_Nil: forall t,
    convert_expr (t_Nil t) ut_Nil.

