Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.

Inductive typecheck : t_env -> t_expr -> t_type -> Prop :=
  (* ENum *)
  (* EBool *)
  (* EVar *)
  | TC_Num: forall env n,
    typecheck env (ENum n) TNum
  | TC_Bool: forall env b,
    typecheck env (EBool b) TBool
  | TC_Var: forall env x T,
    env x = Some T ->
    typecheck env (EVar x) T

  (* EIf *)
  | TC_If: forall env c e1 e2 T,
    typecheck env c TBool ->
    typecheck env e1 T ->
    typecheck env e2 T ->
    typecheck env (EIf c e1 e2) T

  (* EFun *)
  | TC_Fun: forall env x x_T e e_T,
    typecheck (update env x x_T) e e_T ->
    typecheck env (EFun x x_T e) (TFun x_T e_T)

  (* ECall *)
  | TC_Call: forall env f e e_T T,
    typecheck env f (TFun e_T T) ->
    typecheck env e e_T ->
    typecheck env (ECall f e) T

  (* ECons *)
  | TC_Cons: forall env hd tl T,
    typecheck env hd T ->
    typecheck env tl (TList T) ->
    typecheck env (ECons hd tl) (TList T)

  (* ENil *)
  | TC_Nil: forall env T,
    typecheck env (ENil T) (TList T)

  (* EBinop *)
  | TC_Binop_nnn: forall env op e1 e2,
    op = OpPlus \/
    op = OpMinus ->
    typecheck env e1 TNum ->
    typecheck env e2 TNum ->
    typecheck env (EBinop op e1 e2) TNum

  | TC_Binop_nnb: forall env op e1 e2,
    op = OpEq \/
    op = OpNeq ->
    typecheck env e1 TNum ->
    typecheck env e2 TNum ->
    typecheck env (EBinop op e1 e2) TBool

  | TC_Binop_bbb: forall env op e1 e2,
    op = OpAnd \/
    op = OpOr ->
    typecheck env e1 TBool ->
    typecheck env e2 TBool ->
    typecheck env (EBinop op e1 e2) TBool.
