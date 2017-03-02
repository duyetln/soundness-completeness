Require Import String.
Require Import List.

Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Require Import Maps.

(* concrete type used for type checker *)
Inductive cont_type : Type :=
  | cont_Num: cont_type
  | cont_Bool: cont_type
  | cont_Fun: cont_type -> cont_type -> cont_type
  | cont_List: cont_type -> cont_type.

(* inferred type used for type inferencer *)
Inductive inft_type : Type :=
  | inft_Num: inft_type
  | inft_Bool: inft_type
  | inft_Fun: inft_type -> inft_type -> inft_type
  | inft_List: inft_type -> inft_type
  | inft_Var: id -> inft_type. (* id from Maps.v *)

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
  | t_Fun: id -> cont_type -> t_expr -> t_expr
  | t_Call: t_expr -> t_expr -> t_expr
  | t_Binop: binop -> t_expr -> t_expr -> t_expr
  | t_Cons: t_expr -> t_expr -> t_expr
  | t_Nil: cont_type -> t_expr.

Definition tc_env := partial_map cont_type.
Definition ti_env := partial_map inft_type.
Definition constr := list (inft_type * inft_type) % type.
Definition substs := list (id * inft_type) % type.

Inductive convert_type : inft_type -> cont_type -> Prop :=
  | CT_Num: convert_type inft_Num cont_Num
  | CT_Bool: convert_type inft_Bool cont_Bool
  | CT_Fun:
    forall x e x_t e_t,
    convert_type x x_t ->
    convert_type e e_t ->
    convert_type (inft_Fun x e) (cont_Fun x_t e_t)
  | CT_List:
    forall l l_t,
    convert_type l l_t ->
    convert_type (inft_List l) (cont_List l_t).

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

