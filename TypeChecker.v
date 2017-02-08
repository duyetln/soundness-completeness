Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.

Inductive typecheck : t_expr -> environment -> type -> Prop :=
  (* t_Num *)
  (* t_Bool *)
  (* t_Var *)
  | TC_Num: forall env n,
    typecheck (t_Num n) env TNum
  | TC_Bool: forall env b,
    typecheck (t_Bool b) env TBool
  | TC_Var: forall env x T,
    env x = Some T -> typecheck (t_Var x) env T

  (* t_If *)
  | TC_If: forall env c e1 e2 T,
    typecheck c env TBool ->
    typecheck e1 env T ->
    typecheck e2 env T ->
    typecheck (t_If c e1 e2) env T

  (* t_Fun *)
  | TC_Fun: forall env x x_T e e_T,
    typecheck e (update env x x_T) e_T ->
    typecheck (t_Fun x x_T e) env (TFun x_T e_T)

  (* t_Call *)
  | TC_Call: forall env f e e_T T,
    typecheck f env (TFun e_T T) ->
    typecheck e env e_T ->
    typecheck (t_Call f e) env T

  (* t_Cons *)
  | TC_Cons: forall env hd tl T,
    typecheck hd env T ->
    typecheck tl env (TList T) ->
    typecheck (t_Cons hd tl) env (TList T)

  (* t_Nil *)
  | TC_Nil: forall env T,
    typecheck (t_Nil T) env (TList T)

  (* t_Binop *)
  | TC_Binop_nnn: forall env op e1 e2,
    op = op_Plus \/
    op = op_Minus \/
    op = op_Mult \/
    op = op_Div \/
    op = op_Mod ->
    typecheck e1 env TNum ->
    typecheck e2 env TNum ->
    typecheck (t_Binop op e1 e2) env TNum

  | TC_Binop_nnb: forall env op e1 e2,
    op = op_Eq \/
    op = op_Neq \/
    op = op_Lt \/
    op = op_Gt ->
    typecheck e1 env TNum ->
    typecheck e2 env TNum ->
    typecheck (t_Binop op e1 e2) env TBool

  | TC_Binop_bbb: forall env op e1 e2,
    op = op_And \/
    op = op_Or ->
    typecheck e1 env TBool ->
    typecheck e2 env TBool ->
    typecheck (t_Binop op e1 e2) env TBool.
