Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.
Require Import Util.

Definition environment := (@dict string (type * bool)) % type. (* bool indicates if it is let-bound variable *)
Definition constraint := (list (type * type)) % type.

Inductive typed_expr : Type :=
  | TpNum : nat -> type -> typed_expr
  | TpBool : bool -> type -> typed_expr
  | TpVar : string -> type -> typed_expr
  | TpIf : typed_expr -> typed_expr -> typed_expr -> type -> typed_expr
  | TpFun : string -> type -> typed_expr -> type -> typed_expr
  | TpCall : typed_expr -> typed_expr -> type -> typed_expr
  | TpBinop : binop -> typed_expr -> typed_expr -> type -> typed_expr
  | TpCons : typed_expr -> typed_expr -> type -> typed_expr
  | TpNil : type -> typed_expr.

Definition type_from_typed_expr  (texpr : typed_expr) : type :=
  match texpr with
    | TpNum _ t => t
    | TpBool _ t => t
    | TpVar _ t => t
    | TpIf _ _ _ t => t
    | TpFun _ _ _ t => t
    | TpCall _ _ t => t
    | TpBinop _ _ _ t => t
    | TpCons _ _ t => t
    | TpNil t => t
  end.

Definition type_from_env (x : string) (env : environment) : option ((type * bool) % type) :=
  dict_get x str_eqb env.

Fixpoint copy_type (t : type) (fv : nat) (d : @dict nat nat): (nat * type * (@dict nat nat)) % type :=
  match t with
    | TNum => (fv, t, d)
    | TBool => (fv, t, d)
    | TFun x e =>
      let '(x_fv, x_t, d1) := copy_type x fv d in
      let '(e_fv, e_t, d2) := copy_type e x_fv d1 in
        (e_fv, (TFun x_t e_t), d2)
    | TList l =>
      let '(l_fv, l_t, d1) := copy_type l fv d in
        (l_fv, (TList l_t), d1)
    | TVar x =>
      match dict_get x eqb d with
        | None => ((fv + 1), (TVar fv), (x, fv)::d)
        | Some v => (fv, (TVar v), d)
      end
  end.

Fixpoint assign_type (ex : expr) (fv : nat) (env : environment) : option (nat * typed_expr) % type :=
   match ex with
    (* TmNum *)
    | TmNum n => Some (fv, (TpNum n TNum))

    (* TmBool *)
    | TmBool b => Some (fv, (TpBool b TBool))

    (* TmVar *) (* must copy *)
    | TmVar x =>
      match type_from_env x env with
      | Some (t, b) => Some (fv, TpVar x t)
      | None => None
      end

    (* TmIf *)
    | TmIf c e1 e2 =>
      match assign_type c fv env with
        | Some (c_fv, c_tex) =>
          match assign_type e1 c_fv env with
            | Some (e1_fv, e1_tex) =>
              match assign_type e2 e1_fv env with
                | Some (e2_fv, e2_tex) => Some (e2_fv + 1, (TpIf c_tex e1_tex e2_tex (TVar e2_fv)))
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end

    (* TmFun *)
    | TmFun x tx e =>
      let (x_tv, x_fv) :=
        match tx with
          | Some t => (t, fv)
          | None => (TVar fv, fv + 1)
        end
      in
        match assign_type e x_fv ((x, (x_tv, false))::env) with
          | Some (e_fv, e_tex) => Some (e_fv + 1, TpFun x x_tv e_tex (TFun x_tv (TVar e_fv)))
          | None => None
        end

    (* TmCall *)
    | TmCall f x =>
      match assign_type f fv env with
        | Some (f_fv, f_tex) =>
          match assign_type x f_fv env with
            | Some (x_fv, x_tex) => Some (x_fv + 1, (TpCall f_tex x_tex (TVar x_fv)))
            | None => None
          end
        | None => None
      end

    (* TmBinop *)
    | TmBinop op e1 e2 =>
      match assign_type e1 fv env with
        | Some (e1_fv, e1_tex) =>
          match assign_type e2 e1_fv env with
            | Some (e2_fv, e2_tex) => Some (e2_fv + 1, (TpBinop op e1_tex e2_tex (TVar e2_fv)))
            | None => None
          end
        | None => None
      end

    (* TmCons *)
    | TmCons h t =>
      match assign_type h fv env with
        | Some (h_fv, h_tex) =>
          match assign_type t h_fv env with
            | Some (t_fv, t_tex) => Some (t_fv + 1, (TpCons h_tex t_tex (TList (TVar t_fv))))
            | None => None
          end
        | None => None
      end

    (* TmNil *)
    | TmNil => Some (fv + 1, (TpNil (TList (TVar fv))))
  end.

Fixpoint collect_constraint (texpr : typed_expr) : constraint :=
  match texpr with
    (* TpNum *)
    (* TpBool *)
    (* TpVar *)
    | TpNum _ _
    | TpBool _ _
    | TpVar _ _ => []

    (* TpIf *)
    | TpIf c e1 e2 t =>
      let c_t := type_from_typed_expr c in
      let e1_t := type_from_typed_expr e1 in
      let e2_t := type_from_typed_expr e2 in
        (collect_constraint e2) ++
        (collect_constraint e1) ++
        (t, e1_t)::(e1_t, e2_t)::(c_t, TBool)::[]

    (* TpFun *)
    | TpFun _ x_t e t =>
      let e_t := type_from_typed_expr e in
        (collect_constraint e) ++ (t, TFun x_t e_t)::[]

    (* TpCall *)
    | TpCall f e t =>
      let f_t := type_from_typed_expr f in
      let e_t := type_from_typed_expr e in
        (collect_constraint e) ++
        (collect_constraint f) ++
        (f_t, TFun e_t t)::[]

    (* TpBinop *)
    | TpBinop op e1 e2 t =>
      let e1_t := type_from_typed_expr e1 in
      let e2_t := type_from_typed_expr e2 in
      let op_c :=
        match op with
          | OpPlus | OpMinus | OpMult | OpDiv | OpMod =>
            (t, TNum)::(e2_t, TNum)::(e1_t, TNum)::[]
          | OpEq | OpNeq | OpLt | OpGt =>
            (t, TBool)::(e2_t, TNum)::(e1_t, TNum)::[]
          | OpAnd | OpOr =>
            (t, TBool)::(e2_t, TBool)::(e1_t, TBool)::[]
        end
      in
        (collect_constraint e2) ++ (collect_constraint e1) ++ op_c

    (* TpCons *)
    | TpCons hd tl t =>
      let hd_t := type_from_typed_expr hd in
      let tl_t := type_from_typed_expr tl in
        (collect_constraint tl) ++
        (collect_constraint hd) ++
        (tl_t, TList hd_t)::(t, TList hd_t)::[]

    (* TpNil *)
    | TpNil _ => []
  end.
