Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.


Inductive _typeinf : environment -> nat -> ut_expr -> (nat * type * constraint) % type -> Prop :=
  (* ut_Num *)
  (* ut_Bool *)
  (* ut_Var *)
  | TI_Num: forall env n fv,
    _typeinf env fv  (ut_Num n) (fv, TNum, [])
  | TI_Bool: forall env b fv,
    _typeinf env fv  (ut_Bool b) (fv, TBool, [])
  | TI_Var: forall env x fv T,
    env x = Some T -> _typeinf env fv (ut_Var x) (fv, T, [])

  (* ut_If *)
  | TI_If:
    forall env fv
      c c_fv c_C c_T
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    _typeinf env fv c (c_fv, c_T, c_C) ->
    _typeinf env c_fv  e1 (e1_fv, e1_T, e1_C) ->
    _typeinf env e1_fv  e2 (e2_fv, e2_T, e2_C) ->
    _typeinf env fv (ut_If c e1 e2) (e2_fv, e1_T, e2_C ++ e1_C ++ c_C ++ [(e1_T, e2_T); (c_T, TBool)])

  (* ut_Fun *)
  | TI_Fun:
    forall env fv
      x e e_fv e_C e_T,
    _typeinf (update env x (TVar (Id fv))) (fv + 1)  e (e_fv, e_T, e_C) ->
    _typeinf env fv (ut_Fun x e) (e_fv, (TFun (TVar (Id fv)) e_T), e_C)

  (* ut_Call *)
  | TI_Call:
    forall env fv
      f f_fv f_C f_T
      e e_fv e_C e_T,
    _typeinf env fv f (f_fv, f_T, f_C) ->
    _typeinf env f_fv e (e_fv, e_T, e_C) ->
    _typeinf env fv (ut_Call f e) (e_fv + 1, TVar (Id e_fv), e_C ++ f_C ++ [(f_T, TFun e_T (TVar (Id e_fv)))])

  (* ut_Cons *)
  | TI_Cons:
    forall env fv
      hd hd_fv hd_C hd_T
      tl tl_fv tl_C tl_T,
    _typeinf env fv hd (hd_fv, hd_T, hd_C) ->
    _typeinf env hd_fv tl (tl_fv, tl_T, tl_C) ->
    _typeinf env fv (ut_Cons hd tl) (tl_fv, TList hd_T, tl_C ++ hd_C ++ [(tl_T, TList hd_T)])

  (* ut_Nil *)
  | TI_Nil:
    forall env fv,
    _typeinf env fv ut_Nil (fv + 1, TList (TVar (Id fv)), [])

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
    _typeinf env fv e1 (e1_fv, e1_T, e1_C) ->
    _typeinf env e1_fv e2 (e2_fv, e2_T, e2_C) ->
    _typeinf env fv (ut_Binop op e1 e2) (e2_fv, TNum, e2_C++ e1_C ++ [(e2_T, TNum); (e1_T, TNum)])

  | TI_Binop_nnb:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    op = op_Eq \/
    op = op_Neq \/
    op = op_Lt \/
    op = op_Gt ->
    _typeinf env fv e1 (e1_fv, e1_T, e1_C) ->
    _typeinf env e1_fv e2 (e2_fv, e2_T, e2_C) ->
    _typeinf env fv (ut_Binop op e1 e2) (e2_fv, TBool, e2_C++ e1_C ++ [(e2_T, TNum); (e1_T, TNum)])

  | TI_Binop_bbb:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    op = op_And \/
    op = op_Or ->
    _typeinf env fv e1 (e1_fv, e1_T, e1_C) ->
    _typeinf env e1_fv e2 (e2_fv, e2_T, e2_C) ->
    _typeinf env fv (ut_Binop op e1 e2) (e2_fv, TBool, e2_C++ e1_C ++ [(e2_T, TBool); (e1_T, TBool)]).

(* this is ugly *)
Inductive typeinf : ut_expr -> (type * constraint) % type -> Prop :=
  | Wrap: forall e n C T,
    _typeinf (@empty type) 0 e (n, T, C) -> typeinf e (T, C).


(* Process constraints from right to left *)
Inductive unify : constraint -> substitution -> Prop :=
  | U_Empty: unify [] []

  (* (TNum, TNum) *)
  | U_NumNum:
    forall t1 t2 tl tl_sub,
    unify tl tl_sub ->
    apply tl_sub t1 = TNum ->
    apply tl_sub t2 = TNum ->
    unify ((t1, t2)::tl) tl_sub

  (* (TBool, TBool) *)
  | U_BoolBool:
    forall t1 t2 tl tl_sub,
    unify tl tl_sub ->
    apply tl_sub t1 = TBool ->
    apply tl_sub t2 = TBool ->
    unify ((t1, t2)::tl) tl_sub

  (* (TFun x1 e1, TFun x2 e2) *)
  | U_FunFun:
    forall t1 t2 tl tl_sub
      x1 e1 x2 e2 fun_sub,
    unify tl tl_sub ->
    apply tl_sub t1 = TFun x1 e1 ->
    apply tl_sub t2 = TFun x2 e2 ->
    unify [(x1, x2);(e1, e2)] fun_sub ->
    unify ((t1, t2)::tl) (fun_sub ++ tl_sub)

  (* (TList l1, TList l2) *)
  | U_ListList:
    forall t1 t2 tl tl_sub
      l1 l2 list_sub,
    unify tl tl_sub ->
    apply tl_sub t1 = TList l1 ->
    apply tl_sub t2 = TList l2 ->
    unify [(l1, l2)] list_sub ->
    unify ((t1, t2)::tl) (list_sub ++ tl_sub)

  (* (TVar id1, TVar id2) *)
  | U_VarVar:
    forall t1 t2 tl tl_sub
      id1 id2,
    unify tl tl_sub ->
    apply tl_sub t1 = TVar id1 ->
    apply tl_sub t2 = TVar id2 ->
    beq_id id1 id2 = true ->
    unify ((t1, t2)::tl) tl_sub

  (* (TVar x, _) *)
  | U_VarLeft:
    forall t1 t2 tl tl_sub
      x T,
    unify tl tl_sub ->
    apply tl_sub t1 = TVar x ->
    apply tl_sub t2 = T ->
    occurs x T = false ->
    unify ((t1, t2)::tl) ((x, T)::tl_sub)

  (* (_, TVar x) *)
  | U_VarRight:
    forall t1 t2 tl tl_sub
      x T,
    unify tl tl_sub ->
    apply tl_sub t1 = T ->
    apply tl_sub t2 = TVar x ->
    occurs x T = false ->
    unify ((t1, t2)::tl) ((x, T)::tl_sub).
