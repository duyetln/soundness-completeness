Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Maps.


Inductive typeinf : t_env -> nat -> t_expr -> (nat * t_type * constr) % type -> Prop :=
  (* ENum *)
  (* EBool *)
  (* EVar *)
  | TI_Num: forall env n fv,
    typeinf env fv (ENum n) (fv, TNum, [])
  | TI_Bool: forall env b fv,
    typeinf env fv (EBool b) (fv, TBool, [])
  | TI_Var: forall env x fv T,
    env x = Some T -> typeinf env fv (EVar x) (fv, T, [])

  (* EIf *)
  | TI_If:
    forall env fv
      c c_fv c_C c_T
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    typeinf env fv c (c_fv, c_T, c_C) ->
    typeinf env c_fv  e1 (e1_fv, e1_T, e1_C) ->
    typeinf env e1_fv  e2 (e2_fv, e2_T, e2_C) ->
    typeinf env fv (EIf c e1 e2) (e2_fv, e1_T, e2_C ++ e1_C ++ c_C ++ [(e1_T, e2_T); (c_T, TBool)])

  (* EFun *)
  | TI_Fun:
    forall env fv
      x x_T e e_fv e_C e_T,
    typeinf (update env x x_T) fv  e (e_fv, e_T, e_C) ->
    typeinf env fv (EFun x x_T e) (e_fv, (TFun x_T e_T), e_C)

  (* ECall *)
  | TI_Call:
    forall env fv
      f f_fv f_C f_T
      e e_fv e_C e_T,
    typeinf env fv f (f_fv, f_T, f_C) ->
    typeinf env f_fv e (e_fv, e_T, e_C) ->
    typeinf env fv (ECall f e) (e_fv + 1, TVar (Id e_fv), e_C ++ f_C ++ [(f_T, TFun e_T (TVar (Id e_fv)))])

  (* ECons *)
  | TI_Cons:
    forall env fv
      hd hd_fv hd_C hd_T
      tl tl_fv tl_C tl_T,
    typeinf env fv hd (hd_fv, hd_T, hd_C) ->
    typeinf env hd_fv tl (tl_fv, tl_T, tl_C) ->
    typeinf env fv (ECons hd tl) (tl_fv, TList hd_T, tl_C ++ hd_C ++ [(tl_T, TList hd_T)])

  (* ENil *)
  | TI_Nil:
    forall env T fv,
    typeinf env fv (ENil T) (fv, TList T, [])

  (* EBinop *)
  | TI_Binop_nnn:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    typeinf env fv e1 (e1_fv, e1_T, e1_C) ->
    typeinf env e1_fv e2 (e2_fv, e2_T, e2_C) ->
    op = OpPlus \/
    op = OpMinus ->
    typeinf env fv (EBinop op e1 e2) (e2_fv, TNum, e2_C++ e1_C ++ [(e2_T, TNum); (e1_T, TNum)])

  | TI_Binop_nnb:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    typeinf env fv e1 (e1_fv, e1_T, e1_C) ->
    typeinf env e1_fv e2 (e2_fv, e2_T, e2_C) ->
    op = OpEq \/
    op = OpNeq ->
    typeinf env fv (EBinop op e1 e2) (e2_fv, TBool, e2_C++ e1_C ++ [(e2_T, TNum); (e1_T, TNum)])

  | TI_Binop_bbb:
    forall env fv op
      e1 e1_fv e1_C e1_T
      e2 e2_fv e2_C e2_T,
    typeinf env fv e1 (e1_fv, e1_T, e1_C) ->
    typeinf env e1_fv e2 (e2_fv, e2_T, e2_C) ->
    op = OpAnd \/
    op = OpOr ->
    typeinf env fv (EBinop op e1 e2) (e2_fv, TBool, e2_C++ e1_C ++ [(e2_T, TBool); (e1_T, TBool)]).

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

Inductive t_expr : Type := (* t_expr : typed expression *)
  | ENum: nat -> t_expr
  | EBool: bool -> t_expr
  | EVar: id -> t_expr
  | EIf: t_expr -> t_expr -> t_expr -> t_expr
  | EFun: id -> t_type -> t_expr -> t_expr
  | ECall: t_expr -> t_expr -> t_expr
  | EBinop: binop -> t_expr -> t_expr -> t_expr
  | ECons: t_expr -> t_expr -> t_expr
  | ENil: t_type -> t_expr.

Definition app_sub_to_env (s : substs) (env : t_env) : id -> option t_type :=
  (fun i =>
    match env i with
      | Some T => Some (app_sub_to_type s T)
      | None => None
    end).

Inductive satisfy : substs -> constr -> Prop :=
  | SOL_Empty: forall s, satisfy s []
  | SOL_NotEmpty:
    forall s t1 t2 tl,
    app_sub_to_type s t1 = app_sub_to_type s t2 ->
    satisfy s tl ->
    satisfy s ((t1, t2)::tl).
