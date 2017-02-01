Require Import String.
Require Import List.

Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Require Import AST.
Require Import Util.

Definition environment := list (string * type) % type.
Definition substitution := list (nat * type) % type.
Definition constraint := list (nat * type) % type.

Inductive typed_expr : Type :=
  | TpNum : nat -> type -> typed_expr
  | TpBool : bool -> type -> typed_expr
  | TpVar : string-> type -> typed_expr
  | TpIf : typed_expr -> typed_expr -> typed_expr -> type -> typed_expr
  | TpNFun : typed_expr -> type -> typed_expr
  | TpUFun : string -> option type -> typed_expr -> type -> typed_expr
  | TpCall : typed_expr -> typed_expr -> type -> typed_expr
  | TpLet : string -> typed_expr -> typed_expr -> type -> typed_expr
  | TpBinop : binop -> typed_expr -> typed_expr -> type -> typed_expr
(*| TpDatum : string -> list typed_expr -> type -> typed_expr
  | TpMatch : typed_expr -> list pattern -> list typed_expr -> type -> typed_expr *)
  | TpCons : typed_expr -> typed_expr -> type -> typed_expr
  | TpNil : type -> typed_expr
  | TpDelay : typed_expr -> type -> typed_expr
  | TpForce : typed_expr -> type -> typed_expr.

Definition type_from_typed_expr  (texpr : typed_expr) : type :=
  match texpr with
    | TpNum _ t => t
    | TpBool _ t => t
    | TpVar _ t => t
    | TpIf _ _ _ t => t
    | TpNFun _ t => t
    | TpUFun _ _ _ t => t
    | TpCall _ _ t => t
    | TpLet _ _ _ t => t
    | TpBinop _ _ _ t => t
(*  | TpDatum _ _ t => t
    | TpMatch _ _ _ t => t *)
    | TpCons _ _ t => t
    | TpNil t => t
    | TpDelay _ t => t
    | TpForce _ t => t
  end.

Fixpoint type_from_env (x : string) (env : environment) : option type :=
  match env with
    | [] => None
    | (v, t)::l => if str_eqb x v then Some t else type_from_env x l
  end.


(* Need environment for TmLet and TmUFun *)
(* Need level for let-polymorphism *)
Fixpoint assign_type (ex : expr) (fv : nat)  : (nat * typed_expr) % type :=
  match ex with
    | TmNum n => pair fv (TpNum n TNum)
    | TmBool b => pair fv (TpBool b TBool)
    | TmVar x => pair (fv + 1) (TpVar x (TVar fv))
    | TmIf c e1 e2 =>
      let (c_fv, c_tex) := assign_type c fv in
      let (e1_fv, e1_tex) := assign_type e1 c_fv in
      let (e2_fv, e2_tex) := assign_type e2 e1_fv in
        pair (e2_fv + 1) (TpIf c_tex e1_tex e2_tex (TVar e2_fv))
    | TmNFun e =>
      let (e_fv, e_tex) := assign_type e fv in
        pair (e_fv + 1) (TpNFun e_tex (TFun TUnit (TVar e_fv)))
    | TmUFun x tx e =>
      let (e_fv, e_tex) := assign_type e fv in
      match tx with
        | Some t => pair (e_fv + 1) (TpUFun x tx e_tex (TFun t (TVar e_fv)))
        | None => pair (e_fv + 2) (TpUFun x tx e_tex (TFun (TVar e_fv) (TVar (e_fv + 1))))
      end
    | TmCall f x =>
      let (f_fv, f_tex) := assign_type f fv in
      let (x_fv, x_tex) := assign_type x f_fv in
        pair (x_fv + 1) (TpCall (f_tex) (x_tex) (TVar (x_fv)))
    | TmLet x e1 e2 =>
      let (e1_fv, e1_tex) := assign_type e1 fv in
      let (e2_fv, e2_tex) := assign_type e2 e1_fv in
        pair (e2_fv + 1) (TpLet x e1_tex e2_tex (TVar (e2_fv)))
    | TmBinop op e1 e2 =>
      let (e1_fv, e1_tex) := assign_type e1 fv in
      let (e2_fv, e2_tex) := assign_type e2 e1_fv in
        pair (e2_fv + 1) (TpBinop op e1_tex e2_tex (TVar e2_fv))
(*  | TmDatum d l =>
      match l with
        | [] => pair fv (TpDatum d [] (TDatum d []))
        | _::_ =>
          (* l_ex and p_ex are lists of typed_expr *)
          let (l_fv, l_ex) := fold_left (fun (p : (nat * list typed_expr) % type) (e : expr) =>
            let (p_fv, p_ex) := p in
            let (e_fv, e_ex) := assign_type e p_fv in
              pair e_fv (p_ex ++ [e_ex])) l (pair fv []) in

          let (tv_fv, tv_l) := fold_left (fun (p : (nat * list type) % type) (e : expr) =>
            let (p_fv, p_l) := p in
              pair (p_fv + 1) (p_l ++ [TVar p_fv])) l (pair l_fv []) in
          pair tv_fv (TpDatum d l_ex (TDatum d tv_l))
      end *)
    | TmCons h t =>
      let (h_fv, h_tex) := assign_type h fv in
      let (t_fv, t_tex) := assign_type t h_fv in
        pair (t_fv + 1) (TpCons h_tex t_tex (TList (TVar t_fv)))
    | TmNil => pair (fv + 1) (TpNil (TList (TVar fv)))
    | TmForce e =>
      let (e_fv, e_tex) := assign_type e fv in
        pair (e_fv + 1) (TpForce e_tex (TVar e_fv))
    | TmDelay e =>
      let (e_fv, e_tex) := assign_type e fv in
        pair (e_fv + 1) (TpDelay e_tex (TVar e_fv))
  end.
