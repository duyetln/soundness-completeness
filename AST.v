Require Import String.
Require Import List.

Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Require Import Maps.

Inductive type : Type :=
  | TNum: type
  | TBool: type
  | TFun: type -> type -> type
  | TList: type -> type
  | TVar: id -> type. (* id from Maps.v *)

Inductive binop : Type :=
  | op_Plus: binop
  | op_Minus: binop
  | op_Mult: binop
  | op_Div: binop
  | op_Mod: binop
  | op_Eq: binop
  | op_Neq: binop
  | op_Lt: binop
  | op_Gt: binop
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
  | t_Fun: id -> type -> t_expr -> t_expr
  | t_Call: t_expr -> t_expr -> t_expr
  | t_Binop: binop -> t_expr -> t_expr -> t_expr
  | t_Cons: t_expr -> t_expr -> t_expr
  | t_Nil: type -> t_expr.

Definition environment := partial_map type.
Definition constraint := list (type * type) % type.
Definition substitution := list (id * type) % type.

Fixpoint vartype (t : type) : bool :=
  match t with
    | TNum | TBool => false
    | TFun x e => orb (vartype x) (vartype e)
    | TList l => vartype l
    | TVar x => true
  end.

Inductive erase : t_expr -> ut_expr -> Prop :=
  | E_Num: forall n, erase (t_Num n) (ut_Num n)
  | E_Bool: forall b, erase (t_Bool b) (ut_Bool b)
  | E_Var: forall x, erase (t_Var x) (ut_Var x)
  | E_If: forall c c_e e1 e1_e e2 e2_e,
    erase c c_e ->
    erase e1 e1_e ->
    erase e2 e2_e ->
    erase (t_If c e1 e2) (ut_If c_e e1_e e2_e)
  | E_Fun: forall x t e e_e,
    vartype t = false ->
    erase e e_e ->
    erase (t_Fun x t e) (ut_Fun x e_e)
  | E_Call: forall f f_e e e_e,
    erase f f_e ->
    erase e e_e ->
    erase (t_Call f e) (ut_Call f_e e_e)
  | E_Binop: forall op e1 e1_e e2 e2_e,
    erase e1 e1_e ->
    erase e2 e2_e ->
    erase (t_Binop op e1 e2) (ut_Binop op e1_e e2_e)
  | E_Cons: forall hd hd_e tl tl_e,
    erase hd hd_e ->
    erase tl tl_e ->
    erase (t_Cons hd tl) (ut_Cons hd_e tl_e)
  | E_Nil: forall t,
    vartype t = false ->
    erase (t_Nil t) ut_Nil.

