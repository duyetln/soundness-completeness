Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.


Inductive typeinf : t_env -> nat -> ut_expr -> (nat * t_type * constr) % type -> Prop :=
  (* ut_Num *)
  (* ut_Bool *)
  (* ut_Var *)
  | TI_Num: forall env n fv,
    typeinf env fv (ut_Num n) (fv, TNum, [])
  | TI_Bool: forall env b fv,
    typeinf env fv (ut_Bool b) (fv, TBool, [])
  | TI_Var: forall env x fv T,
    env x = Some T -> typeinf env fv (ut_Var x) (fv, T, [])

  (* ut_If *)
  | TI_If:
    forall env fv
      c c_fv c_C c_T
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    typeinf env fv c (c_fv, c_T, c_C) ->
    typeinf env c_fv  e1 (e1_fv, e1_T, e1_C) ->
    typeinf env e1_fv  e2 (e2_fv, e2_T, e2_C) ->
    typeinf env fv (ut_If c e1 e2) (e2_fv, e1_T, e2_C ++ e1_C ++ c_C ++ [(e1_T, e2_T); (c_T, TBool)])

  (* ut_Fun *)
  | TI_Fun:
    forall env fv
      x e e_fv e_C e_T,
    typeinf (update env x (TVar (Id fv))) (fv + 1)  e (e_fv, e_T, e_C) ->
    typeinf env fv (ut_Fun x e) (e_fv, (TFun (TVar (Id fv)) e_T), e_C)

  (* ut_Call *)
  | TI_Call:
    forall env fv
      f f_fv f_C f_T
      e e_fv e_C e_T,
    typeinf env fv f (f_fv, f_T, f_C) ->
    typeinf env f_fv e (e_fv, e_T, e_C) ->
    typeinf env fv (ut_Call f e) (e_fv + 1, TVar (Id e_fv), e_C ++ f_C ++ [(f_T, TFun e_T (TVar (Id e_fv)))])

  (* ut_Cons *)
  | TI_Cons:
    forall env fv
      hd hd_fv hd_C hd_T
      tl tl_fv tl_C tl_T,
    typeinf env fv hd (hd_fv, hd_T, hd_C) ->
    typeinf env hd_fv tl (tl_fv, tl_T, tl_C) ->
    typeinf env fv (ut_Cons hd tl) (tl_fv, TList hd_T, tl_C ++ hd_C ++ [(tl_T, TList hd_T)])

  (* ut_Nil *)
  | TI_Nil:
    forall env fv,
    typeinf env fv ut_Nil (fv + 1, TList (TVar (Id fv)), [])

  (* ut_Binop *)
  | TI_Binop_nnn:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    typeinf env fv e1 (e1_fv, e1_T, e1_C) ->
    typeinf env e1_fv e2 (e2_fv, e2_T, e2_C) ->
    op = op_Plus \/
    op = op_Minus ->
    typeinf env fv (ut_Binop op e1 e2) (e2_fv, TNum, e2_C++ e1_C ++ [(e2_T, TNum); (e1_T, TNum)])

  | TI_Binop_nnb:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    typeinf env fv e1 (e1_fv, e1_T, e1_C) ->
    typeinf env e1_fv e2 (e2_fv, e2_T, e2_C) ->
    op = op_Eq \/
    op = op_Neq ->
    typeinf env fv (ut_Binop op e1 e2) (e2_fv, TBool, e2_C++ e1_C ++ [(e2_T, TNum); (e1_T, TNum)])

  | TI_Binop_bbb:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    typeinf env fv e1 (e1_fv, e1_T, e1_C) ->
    typeinf env e1_fv e2 (e2_fv, e2_T, e2_C) ->
    op = op_And \/
    op = op_Or ->
    typeinf env fv (ut_Binop op e1 e2) (e2_fv, TBool, e2_C++ e1_C ++ [(e2_T, TBool); (e1_T, TBool)]).

Fixpoint subst (s : (id * t_type) % type) (t : t_type) : t_type :=
  match t with
    | TNum | TBool => t
    | TFun x e => TFun (subst s x) (subst s e)
    | TList l => TList (subst s l)
    | TVar x => let (i, sub) := s in if beq_id i x then sub else t
  end.

Definition app_substs (sub : substs) (tp : t_type) : t_type :=
  fold_right (fun s t => subst s t) tp sub.

Inductive solution : substs -> constr -> Prop :=
  | SOL_Empty: forall s, solution s []
  | SOL_NotEmpty:
    forall s t1 t2 tl,
    app_substs s t1 = app_substs s t2 ->
    solution s tl ->
    solution s ((t1, t2)::tl).
