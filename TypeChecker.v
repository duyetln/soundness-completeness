Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.

Inductive typecheck : tc_env -> t_expr -> cont_type -> Prop :=
  (* t_Num *)
  (* t_Bool *)
  (* t_Var *)
  | TC_Num: forall env n,
    typecheck env (t_Num n) cont_Num
  | TC_Bool: forall env b,
    typecheck env (t_Bool b) cont_Bool
  | TC_Var: forall env x T,
    env x = Some T ->
    typecheck env (t_Var x) T

  (* t_If *)
  | TC_If: forall env c e1 e2 T,
    typecheck env c cont_Bool ->
    typecheck env e1 T ->
    typecheck env e2 T ->
    typecheck env (t_If c e1 e2) T

  (* t_Fun *)
  | TC_Fun: forall env x x_T e e_T,
    typecheck (update env x x_T) e e_T ->
    typecheck env (t_Fun x x_T e) (cont_Fun x_T e_T)

  (* t_Call *)
  | TC_Call: forall env f e e_T T,
    typecheck env f (cont_Fun e_T T) ->
    typecheck env e e_T ->
    typecheck env (t_Call f e) T

  (* t_Cons *)
  | TC_Cons: forall env hd tl T,
    typecheck env hd T ->
    typecheck env tl (cont_List T) ->
    typecheck env (t_Cons hd tl) (cont_List T)

  (* t_Nil *)
  | TC_Nil: forall env T,
    typecheck env (t_Nil T) (cont_List T)

  (* t_Binop *)
  | TC_Binop_nnn: forall env op e1 e2,
    op = op_Plus \/
    op = op_Minus ->
    typecheck env e1 cont_Num ->
    typecheck env e2 cont_Num ->
    typecheck env (t_Binop op e1 e2) cont_Num

  | TC_Binop_nnb: forall env op e1 e2,
    op = op_Eq \/
    op = op_Neq ->
    typecheck env e1 cont_Num ->
    typecheck env e2 cont_Num ->
    typecheck env (t_Binop op e1 e2) cont_Bool

  | TC_Binop_bbb: forall env op e1 e2,
    op = op_And \/
    op = op_Or ->
    typecheck env e1 cont_Bool ->
    typecheck env e2 cont_Bool ->
    typecheck env (t_Binop op e1 e2) cont_Bool.
