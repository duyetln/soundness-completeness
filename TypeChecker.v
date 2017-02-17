Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.

Inductive typecheck : environment -> t_expr -> type -> Prop :=
  (* t_Num *)
  (* t_Bool *)
  (* t_Var *)
  | TC_Num: forall env n,
    typecheck env (t_Num n) TNum
  | TC_Bool: forall env b,
    typecheck env (t_Bool b) TBool
  | TC_Var: forall env x T,
    env x = Some T -> typecheck env (t_Var x) T

  (* t_If *)
  | TC_If: forall env c e1 e2 T,
    typecheck env c TBool ->
    typecheck env e1 T ->
    typecheck env e2 T ->
    typecheck env (t_If c e1 e2) T

  (* t_Fun *)
  | TC_Fun: forall env x x_T e e_T,
    typecheck (update env x x_T) e e_T ->
    typecheck env (t_Fun x x_T e) (TFun x_T e_T)

  (* t_Call *)
  | TC_Call: forall env f e e_T T,
    typecheck env f (TFun e_T T) ->
    typecheck env e e_T ->
    typecheck env (t_Call f e) T

  (* t_Cons *)
  | TC_Cons: forall env hd tl T,
    typecheck env hd T ->
    typecheck env tl (TList T) ->
    typecheck env (t_Cons hd tl) (TList T)

  (* t_Nil *)
  | TC_Nil: forall env T,
    typecheck env (t_Nil T) (TList T)

  (* t_Binop *)
  | TC_Binop_nnn: forall env op e1 e2,
    op = op_Plus \/
    op = op_Minus \/
    op = op_Mult \/
    op = op_Div \/
    op = op_Mod ->
    typecheck env e1 TNum ->
    typecheck env e2 TNum ->
    typecheck env (t_Binop op e1 e2) TNum

  | TC_Binop_nnb: forall env op e1 e2,
    op = op_Eq \/
    op = op_Neq \/
    op = op_Lt \/
    op = op_Gt ->
    typecheck env e1 TNum ->
    typecheck env e2 TNum ->
    typecheck env (t_Binop op e1 e2) TBool

  | TC_Binop_bbb: forall env op e1 e2,
    op = op_And \/
    op = op_Or ->
    typecheck env e1 TBool ->
    typecheck env e2 TBool ->
    typecheck env (t_Binop op e1 e2) TBool.
