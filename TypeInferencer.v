Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Util.

Definition environment := (@dict string type) % type.
Definition constraint := (list (type * type)) % type.

Inductive type_holder : Type :=
  | th_Num : nat -> type -> type_holder
  | th_Bool : bool -> type -> type_holder
  | th_Var : string -> type -> type_holder
  | th_If : type_holder -> type_holder -> type_holder -> type -> type_holder
  | th_Fun : string -> type -> type_holder -> type -> type_holder
  | th_Call : type_holder -> type_holder -> type -> type_holder
  | th_Binop : binop -> type_holder -> type_holder -> type -> type_holder
  | th_Cons : type_holder -> type_holder -> type -> type_holder
  | th_Nil : type -> type_holder.

Definition type_from_type_holder  (th : type_holder) : type :=
  match th with
    | th_Num _ t => t
    | th_Bool _ t => t
    | th_Var _ t => t
    | th_If _ _ _ t => t
    | th_Fun _ _ _ t => t
    | th_Call _ _ t => t
    | th_Binop _ _ _ t => t
    | th_Cons _ _ t => t
    | th_Nil t => t
  end.

Definition type_from_env (x : string) (env : environment) : option type :=
  dict_get x str_eqb env.

Fixpoint assign_type (ex : ut_expr) (fv : nat) (env : environment) : option (nat * type_holder) % type :=
   match ex with
    (* ut_Num *)
    | ut_Num n => Some (fv, (th_Num n TNum))

    (* ut_Bool *)
    | ut_Bool b => Some (fv, (th_Bool b TBool))

    (* ut_Var *)
    | ut_Var x =>
      match type_from_env x env with
      | Some t => Some (fv, th_Var x t)
      | None => None
      end

    (* ut_If *)
    | ut_If c e1 e2 =>
      match assign_type c fv env with
        | Some (c_fv, c_th) =>
          match assign_type e1 c_fv env with
            | Some (e1_fv, e1_th) =>
              match assign_type e2 e1_fv env with
                | Some (e2_fv, e2_th) => Some (e2_fv + 1, (th_If c_th e1_th e2_th (TVar e2_fv)))
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end

    (* ut_Fun *)
    | ut_Fun x e =>
      let (x_tv, x_fv) := (TVar fv, fv + 1) in
        match assign_type e x_fv ((x, x_tv)::env) with
          | Some (e_fv, e_th) => Some (e_fv + 1, th_Fun x x_tv e_th (TFun x_tv (TVar e_fv)))
          | None => None
        end

    (* ut_Call *)
    | ut_Call f x =>
      match assign_type f fv env with
        | Some (f_fv, f_th) =>
          match assign_type x f_fv env with
            | Some (x_fv, x_th) => Some (x_fv + 1, (th_Call f_th x_th (TVar x_fv)))
            | None => None
          end
        | None => None
      end

    (* ut_Binop *)
    | ut_Binop op e1 e2 =>
      match assign_type e1 fv env with
        | Some (e1_fv, e1_th) =>
          match assign_type e2 e1_fv env with
            | Some (e2_fv, e2_th) => Some (e2_fv + 1, (th_Binop op e1_th e2_th (TVar e2_fv)))
            | None => None
          end
        | None => None
      end

    (* ut_Cons *)
    | ut_Cons h t =>
      match assign_type h fv env with
        | Some (h_fv, h_th) =>
          match assign_type t h_fv env with
            | Some (t_fv, t_th) => Some (t_fv + 1, (th_Cons h_th t_th (TList (TVar t_fv))))
            | None => None
          end
        | None => None
      end

    (* ut_Nil *)
    | ut_Nil => Some (fv + 1, (th_Nil (TList (TVar fv))))
  end.

Fixpoint collect_constraint (th : type_holder) : constraint :=
  match th with
    (* th_Num *)
    (* th_Bool *)
    (* th_Var *)
    | th_Num _ _
    | th_Bool _ _
    | th_Var _ _ => []

    (* th_If *)
    | th_If c e1 e2 t =>
      let c_t := type_from_type_holder c in
      let e1_t := type_from_type_holder e1 in
      let e2_t := type_from_type_holder e2 in
        (collect_constraint e2) ++
        (collect_constraint e1) ++
        (t, e1_t)::(e1_t, e2_t)::(c_t, TBool)::[]

    (* th_Fun *)
    | th_Fun _ x_t e t =>
      let e_t := type_from_type_holder e in
        (collect_constraint e) ++ (t, TFun x_t e_t)::[]

    (* th_Call *)
    | th_Call f e t =>
      let f_t := type_from_type_holder f in
      let e_t := type_from_type_holder e in
        (collect_constraint e) ++
        (collect_constraint f) ++
        (f_t, TFun e_t t)::[]

    (* th_Binop *)
    | th_Binop op e1 e2 t =>
      let e1_t := type_from_type_holder e1 in
      let e2_t := type_from_type_holder e2 in
      let op_c :=
        match op with
          | op_Plus | op_Minus | op_Mult | op_Div | op_Mod =>
            (t, TNum)::(e2_t, TNum)::(e1_t, TNum)::[]
          | op_Eq | op_Neq | op_Lt | op_Gt =>
            (t, TBool)::(e2_t, TNum)::(e1_t, TNum)::[]
          | op_And | op_Or =>
            (t, TBool)::(e2_t, TBool)::(e1_t, TBool)::[]
        end
      in
        (collect_constraint e2) ++ (collect_constraint e1) ++ op_c

    (* th_Cons *)
    | th_Cons hd tl t =>
      let hd_t := type_from_type_holder hd in
      let tl_t := type_from_type_holder tl in
        (collect_constraint tl) ++
        (collect_constraint hd) ++
        (t, TList hd_t)::(tl_t, TList hd_t)::[]

    (* th_Nil *)
    | th_Nil _ => []
  end.
