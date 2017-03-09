Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.


Fixpoint app_sub_to_type (s : substs) (t : t_type) : t_type :=
  match t with
    | TNum | TBool => t
    | TFun x e => TFun (app_sub_to_type s x) (app_sub_to_type s e)
    | TList l => TList (app_sub_to_type s l)
    | TVar i =>
      match s i with
        | Some T => T
        | None => t
      end
  end.

Fixpoint app_sub_to_expr (s : substs) (e : t_expr) : t_expr :=
  match e with
    | ENum _ | EBool _ | EVar _ => e
    | EIf c e1 e2 =>
      EIf (app_sub_to_expr s c) (app_sub_to_expr s e1) (app_sub_to_expr s e2)
    | EFun x T e =>
      EFun x (app_sub_to_type s T) (app_sub_to_expr s e)
    | ECall f e =>
      ECall (app_sub_to_expr s f) (app_sub_to_expr s e)
    | EBinop op e1 e2 =>
      EBinop op (app_sub_to_expr s e1) (app_sub_to_expr s e2)
    | ECons hd tl =>
      ECons (app_sub_to_expr s hd) (app_sub_to_expr s tl)
    | ENil T =>
      ENil (app_sub_to_type s T)
  end.

Definition app_sub_to_env (s : substs) (env : t_env) : substs :=
  (fun i =>
    match env i with
      | Some T => Some (app_sub_to_type s T)
      | None => None
    end).

Inductive satisfy : substs -> constr -> Prop :=
  | SAT_Empty: forall s, satisfy s []
  | SAT_NotEmpty:
    forall s t1 t2 tl,
    app_sub_to_type s t1 = app_sub_to_type s t2 ->
    satisfy s tl ->
    satisfy s ((t1, t2)::tl).

Fixpoint delete (s : substs) (l : list id) : substs :=
  match l with
    | [] => s
    | i::tl =>
    match s i with
      | Some _ => delete (t_update s i None) tl
      | None => delete s tl
    end
  end.

Fixpoint pick (t : t_type) (fv : nat) : nat :=
  match t with
    | TNum | TBool => fv
    | TFun x e => pick e (pick x fv)
    | TList l => pick l fv
    | TVar (Id n) => if leb fv n then n + 1 else fv
  end.

Inductive typeinf : t_env -> nat -> t_expr -> (nat * t_type * constr * list id) % type -> Prop :=
  (* ENum *)
  (* EBool *)
  (* EVar *)
  | TI_Num: forall env n fv,
    typeinf env fv (ENum n) (fv, TNum, [], [])
  | TI_Bool: forall env b fv,
    typeinf env fv (EBool b) (fv, TBool, [], [])
  | TI_Var: forall env x fv T,
    env x = Some T -> typeinf env fv (EVar x) (fv, T, [], [])

  (* EIf *)
  | TI_If:
    forall env fv
      c c_fv c_C c_T c_X
      e1 e1_fv e1_C e1_T e1_X
      e2 e2_fv e2_C e2_T e2_X,
    typeinf env fv c (c_fv, c_T, c_C, c_X) ->
    typeinf env c_fv  e1 (e1_fv, e1_T, e1_C, e1_X) ->
    typeinf env e1_fv  e2 (e2_fv, e2_T, e2_C, e2_X) ->
    typeinf env fv (EIf c e1 e2) (e2_fv, e1_T, e2_C ++ e1_C ++ c_C ++ [(e1_T, e2_T); (c_T, TBool)], e2_X ++ e1_X ++ c_X)

  (* EFun *)
  | TI_Fun:
    forall env fv fv'
      x x_T e e_fv e_C e_T e_X,
    pick x_T fv = fv' ->
    typeinf (update env x x_T) fv' e (e_fv, e_T, e_C, e_X) ->
    typeinf env fv (EFun x x_T e) (e_fv, (TFun x_T e_T), e_C, e_X)

  (* ECall *)
  | TI_Call:
    forall env fv
      f f_fv f_C f_T f_X
      e e_fv e_C e_T e_X,
    typeinf env fv f (f_fv, f_T, f_C, f_X) ->
    typeinf env f_fv e (e_fv, e_T, e_C, e_X) ->
    typeinf env fv (ECall f e) (e_fv + 1, TVar (Id e_fv), e_C ++ f_C ++ [(f_T, TFun e_T (TVar (Id e_fv)))], e_X ++ f_X ++ [Id e_fv])

  (* ECons *)
  | TI_Cons:
    forall env fv
      hd hd_fv hd_C hd_T hd_X
      tl tl_fv tl_C tl_T tl_X,
    typeinf env fv hd (hd_fv, hd_T, hd_C, hd_X) ->
    typeinf env hd_fv tl (tl_fv, tl_T, tl_C, tl_X) ->
    typeinf env fv (ECons hd tl) (tl_fv, TList hd_T, tl_C ++ hd_C ++ [(tl_T, TList hd_T)], tl_X ++ hd_X)

  (* ENil *)
  | TI_Nil:
    forall env T fv,
    typeinf env fv (ENil T) (fv, TList T, [], [])

  (* EBinop *)
  | TI_Binop_nnn:
    forall env fv op
      e1 e1_fv e1_C e1_T e1_X
      e2 e2_fv e2_C e2_T e2_X,
    typeinf env fv e1 (e1_fv, e1_T, e1_C, e1_X) ->
    typeinf env e1_fv e2 (e2_fv, e2_T, e2_C, e2_X) ->
    op = OpPlus \/
    op = OpMinus ->
    typeinf env fv (EBinop op e1 e2) (e2_fv, TNum, e2_C++ e1_C ++ [(e2_T, TNum); (e1_T, TNum)], e2_X ++ e1_X)

  | TI_Binop_nnb:
    forall env fv op
      e1 e1_fv e1_C e1_T e1_X
      e2 e2_fv e2_C e2_T e2_X,
    typeinf env fv e1 (e1_fv, e1_T, e1_C, e1_X) ->
    typeinf env e1_fv e2 (e2_fv, e2_T, e2_C, e2_X) ->
    op = OpEq \/
    op = OpNeq ->
    typeinf env fv (EBinop op e1 e2) (e2_fv, TBool, e2_C++ e1_C ++ [(e2_T, TNum); (e1_T, TNum)], e2_X ++ e1_X)

  | TI_Binop_bbb:
    forall env fv op
      e1 e1_fv e1_C e1_T e1_X
      e2 e2_fv e2_C e2_T e2_X,
    typeinf env fv e1 (e1_fv, e1_T, e1_C, e1_X) ->
    typeinf env e1_fv e2 (e2_fv, e2_T, e2_C, e2_X) ->
    op = OpAnd \/
    op = OpOr ->
    typeinf env fv (EBinop op e1 e2) (e2_fv, TBool, e2_C++ e1_C ++ [(e2_T, TBool); (e1_T, TBool)], e2_X ++ e1_X).
