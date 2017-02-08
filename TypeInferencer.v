Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.

Inductive typeinf : ut_expr -> environment -> nat -> (nat * constraint * type) % type -> Prop :=
  (* ut_Num *)
  (* ut_Bool *)
  (* ut_Var *)
  | TI_Num: forall env n fv,
    typeinf (ut_Num n) env fv (fv, [], TNum)
  | TI_Bool: forall env b fv,
    typeinf (ut_Bool b) env fv (fv, [], TBool)
  | TI_Var: forall env x fv T,
    env x = Some T -> typeinf (ut_Var x) env fv (fv, [], T)

  (* ut_If *)
  | TI_If:
    forall env fv
      c c_fv c_C c_T
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    typeinf c env fv (c_fv, c_C, c_T) ->
    typeinf e1 env c_fv (e1_fv, e1_C, e1_T) ->
    typeinf e2 env e1_fv (e2_fv, e2_C, e2_T) ->
    typeinf (ut_If c e1 e2) env fv (e2_fv, [(c_T, TBool); (e1_T, e2_T)] ++ c_C ++ e1_C ++ e2_C, e1_T)

  (* ut_Fun *)
  | TI_Fun:
    forall env fv
      x e e_fv e_C e_T,
    typeinf e (update env x (TVar fv)) (fv + 1) (e_fv, e_C, e_T) ->
    typeinf (ut_Fun x e) env fv (e_fv, e_C, (TFun (TVar fv) e_T))

  (* ut_Call *)
  | TI_Call:
    forall env fv
      f f_fv f_C f_T
      e e_fv e_C e_T,
    typeinf f env fv (f_fv, f_C, f_T) ->
    typeinf e env f_fv (e_fv, e_C, e_T) ->
    typeinf (ut_Call f e) env fv (e_fv + 1, [(f_T, TFun e_T (TVar e_fv))] ++ f_C ++ e_C, TVar e_fv)

  (* ut_Cons *)
  | TI_Cons:
    forall env fv
      hd hd_fv hd_C hd_T
      tl tl_fv tl_C tl_T,
    typeinf hd env fv (hd_fv, hd_C, hd_T) ->
    typeinf tl env hd_fv (tl_fv, tl_C, tl_T) ->
    typeinf (ut_Cons hd tl) env fv (tl_fv, [(tl_T, TList hd_T)] ++ hd_C ++ tl_C, TList hd_T)

  (* ut_Nil *)
  | TI_Nil:
    forall env fv,
    typeinf ut_Nil env fv (fv + 1, [], TList (TVar fv))

  (* ut_Binop *)
  | TI_Binop_nnn:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    op = op_Plus \/
    op = op_Minus \/
    op = op_Mult \/
    op = op_Div \/
    op = op_Mod ->
    typeinf e1 env fv (e1_fv, e1_C, e1_T) ->
    typeinf e2 env e1_fv (e2_fv, e2_C, e2_T) ->
    typeinf (ut_Binop op e1 e2) env fv (e2_fv, [(e1_T, TNum); (e2_T, TNum)] ++ e1_C ++ e2_C, TNum)

  | TI_Binop_nnb:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    op = op_Eq \/
    op = op_Neq \/
    op = op_Lt \/
    op = op_Gt ->
    typeinf e1 env fv (e1_fv, e1_C, e1_T) ->
    typeinf e2 env e1_fv (e2_fv, e2_C, e2_T) ->
    typeinf (ut_Binop op e1 e2) env fv (e2_fv, [(e1_T, TNum); (e2_T, TNum)] ++ e1_C ++ e2_C, TBool)

  | TI_Binop_bbb:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    op = op_And \/
    op = op_Or ->
    typeinf e1 env fv (e1_fv, e1_C, e1_T) ->
    typeinf e2 env e1_fv (e2_fv, e2_C, e2_T) ->
    typeinf (ut_Binop op e1 e2) env fv (e2_fv, [(e1_T, TBool); (e2_T, TBool)] ++ e1_C ++ e2_C, TBool).
