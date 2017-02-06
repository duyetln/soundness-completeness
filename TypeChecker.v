Require Import String.
Require Import List.
Require Import Nat.

Open Scope string_scope.
Open Scope list_scope.
Open Scope core_scope.

Import ListNotations.

Require Import AST.

Fixpoint type_eqb (t1 t2 : type) : bool :=
  match t1, t2 with
    | TNum, TNum => true
    | TBool, TBool => true
    | TFun x1 e1, TFun x2 e2 => andb (type_eqb x1 x2) (type_eqb e1 e2)
    | TList l1, TList l2 => type_eqb l1 l2
    | _, _ => false
  end.

Fixpoint typecheck (ex : t_expr) (env : environment) : option type :=
  match ex with
    (* t_Num *)
    (* t_Bool *)
    (* t_Var *)
    | t_Num _ => Some TNum
    | t_Bool _ => Some TBool
    | t_Var x => type_from_env x env

    (* t_If *)
    | t_If c e1 e2 =>
      match typecheck c env, typecheck e1 env, typecheck e2 env with
        | Some TBool, Some e1_t, Some e2_t =>
          if type_eqb e1_t e2_t then Some e1_t
          else None
        | _, _, _ => None
      end

    (* t_Fun *)
    | t_Fun x x_t e =>
      match typecheck e ((x, x_t)::env) with
        | Some e_t => Some (TFun x_t e_t)
        | _ => None
      end

    (* t_Call *)
    | t_Call f e =>
      match typecheck f env, typecheck e env with
        | Some (TFun t1 t2), Some e_t =>
          if type_eqb t1 e_t then Some t2
          else None
        | _, _ => None
      end

    (* t_Binop *)
    | t_Binop op e1 e2 =>
      match op with
        | op_Plus | op_Minus | op_Mult | op_Div | op_Mod =>
          match typecheck e1 env, typecheck e2 env with
            | Some TNum, Some TNum => Some TNum
            | _, _ => None
          end
        | op_Eq | op_Neq | op_Lt | op_Gt =>
          match typecheck e1 env, typecheck e2 env with
            | Some TNum, Some TNum => Some TBool
            | _, _ => None
          end
        | op_And | op_Or =>
          match typecheck e1 env, typecheck e2 env with
            | Some TBool, Some TBool => Some TBool
            | _, _ => None
          end
      end

    (* t_Cons *)
    | t_Cons hd tl =>
      match typecheck hd env, typecheck tl env with
        | Some hd_t, Some (TList tl_t) =>
          if type_eqb hd_t tl_t then Some (TList hd_t)
          else None
        | _, _ => None
      end

    (* t_Nil *)
    | t_Nil t => Some (TList t)
  end.

Example ex1 : typecheck (t_Num 1) [] = Some TNum.
Proof.
  simpl. reflexivity.
Qed.

Example ex2 : typecheck (t_Bool true) [] = Some TBool.
Proof.
  simpl. reflexivity.
Qed.

Example ex3 : typecheck (t_Cons (t_Num 2) (t_Nil TNum)) [] = Some (TList TNum).
Proof.
  simpl. reflexivity.
Qed.

Example ex4 : typecheck (t_Var "x") (("x", TNum)::[]) = Some TNum.
Proof.
  simpl. reflexivity.
Qed.

Example ex5 : typecheck (t_Fun "x" TNum (t_Binop op_Plus (t_Var "x") (t_Num 2))) [] = Some (TFun TNum TNum).
Proof.
  simpl. reflexivity.
Qed.

Example ex6 : typecheck (t_If (t_Binop op_Lt (t_Num 1) (t_Num 2)) (t_Bool true) (t_Bool false)) [] = Some TBool.
Proof.
  simpl. reflexivity.
Qed.