# I. Introduction

  The goal of this project is to use Coq to prove Soundness and Completeness theorems of constraint typing rules for a simple language. This language is just simply typed lambda calculus (with type variables) and some extensions. The project was inspired by the need to verify the correctness of a type inferencer implementation in a past homework. However, this project is not to verify the full implementation; only abstract constraint typing rules of the implementation are proved in Coq proofs.

# II. About the Code:

  The project code is hosted on [Github](https://github.com/duyetln/soundness-completeness/tree/cs239-final-report) and organized as follows:

  * `LibTactics.v` and `Maps.v`: extra tactics and `partial_map` data structure borrowed from _Software Foundations_ book. Additional utility methods and lemmas are added to `Maps.v`.
  * `AST.v`: definitions of the abstract syntax tree, types, expressions, environment, constraint, and substitution.
  * `TypeChecker.v`: implementation of the type checker.
  * `TypeInferencer.v`: implementation of the type inferencer.
  * `Lemmas.v`: proofs of additional lemmas used in proving the two theorems.
  * `Goals.v`: proofs of Soundness and Completeness.

  For grading purpose, the following git tags have been created: `cs239-wk5-presentation`, `cs239-wk8-presentation`, `cs239-wk10-presentation`, and `cs239-final-report`. They mark the state of the code at the corresponding timeline of the course.

  To compile the code, run the command:

    coqc LibTactics.v Maps.v AST.v TypeChecker.v TypeInferencer.v Lemmas.v Goals.v


# III. Implementation:

  Originally, the language chosen was more extensive than described above. Data structures, list comprehension, `let` expression, pattern matching, and `force` and `delay` expressions were included in the language syntax. To reduce implementation complexity, these features were later removed. The final syntax and types of the language are defined below:

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

    Inductive t_type : Type :=
      | TNum: t_type
      | TBool: t_type
      | TFun: t_type -> t_type -> t_type
      | TList: t_type -> t_type
      | TVar: id -> t_type. (* id from Maps.v *)

  The type checker and type inferencer are implemented as inductive propositions:

    Inductive typecheck : t_env -> t_expr -> t_type -> Prop :=
      | TC_Num: forall env n,
        typecheck env (ENum n) TNum
      ...
      | TC_Var: forall env x T,
        env x = Some T ->
        typecheck env (EVar x) T
      ...
      | TC_Fun: forall env x x_T e e_T,
        typecheck (update env x x_T) e e_T ->
        typecheck env (EFun x x_T e) (TFun x_T e_T)
      | TC_Call: forall env f e e_T T,
        typecheck env f (TFun e_T T) ->
        typecheck env e e_T ->
        typecheck env (ECall f e) T
      ...

    Inductive typeinf : t_env -> nat -> t_expr -> (nat * t_type * constr * list id) % type -> Prop :=
      | TI_Num: forall env n fv,
        typeinf env fv (ENum n) (fv + 1, TNum, [], [])
      ...
      | TI_Var: forall env x fv fv' T,
        env x = Some T ->
        max_typevar T fv + 1 = fv' ->
        typeinf env fv (EVar x) (fv', T, [], [])
      ...
      | TI_Fun:
        forall env fv fv'
          x x_T e e_fv e_C e_T e_X,
        max_typevar x_T fv + 1 = fv' ->
        typeinf (update env x x_T) fv' e (e_fv, e_T, e_C, e_X) ->
        typeinf env fv (EFun x x_T e) (e_fv, (TFun x_T e_T), e_C, e_X)
      | TI_Call:
        forall env fv
          f f_fv f_C f_T f_X
          e e_fv e_C e_T e_X,
        typeinf env fv f (f_fv, f_T, f_C, f_X) ->
        typeinf env f_fv e (e_fv, e_T, e_C, e_X) ->
        typeinf env fv (ECall f e) (e_fv + 1, TVar (Id e_fv), e_C ++ f_C ++ [(f_T, TFun e_T (TVar (Id e_fv)))], e_X ++ f_X ++ [Id e_fv])
      ...

  Previously, the type checker and type inferencer were implemented as functions, together with a `unify` function that from a constraint set produces a substitution satisfying the constraints. However, the implementation of `unify` could not be compiled since Coq was not convinced the function would terminate. Since it was difficult to prove that, `unify` was removed and the type checker and type inferencer were implemented as inductive propositions.

  In addition, functions `app_sub_to_env`, `app_sub_to_type`, and `app_sub_to_expr` are implemented to apply a substitution to an environment, a type, and an expression, respectively.

# IV. Goals:

  Soundness theorem states that if an expression type checks under a type inferencer, then it should also type check under a type checker:

    Theorem typeinference_soundness :
      forall
        e ti_env fv1 fv2 S C X
        sub
        t tc_env T,
      (* if type inferencing on e under ti_env produces S and C... *)
      typeinf ti_env fv1 e (fv2, S, C, X) ->
      (* and sub is a solution for (S, C)... *)
      satisfy sub C ->
      app_sub_to_type sub S = T ->
      (* then after applying sub to the e and ti_env,... *)
      app_sub_to_expr sub e = t ->
      app_sub_to_env sub ti_env = tc_env ->
      (* e should type check under tc_env as well *)
      typecheck tc_env t T.

  Completeness theorem states that if an expression type checks under a type checker, then it should also type check under a type inferencer:

    Theorem typeinference_completeness :
      forall
        e (ti_env : t_env) fv1 fv2 S C X
        sub
        t (tc_env : t_env) T,
      (* if (sub, T) is a solution for (ti_env, e)... *)
      app_sub_to_expr sub e = t ->
      app_sub_to_env sub ti_env = tc_env ->
      typecheck tc_env t T ->
      (* and type inferencing on e under ti_env produces S and C... *)
      typeinf ti_env fv1 e (fv2, S, C, X) ->
      (forall i, In i X -> sub i = None) ->
      (* then there exists a solution for S and C *)
      (exists sub', satisfy sub' C /\ app_sub_to_type sub' S = T /\ omit sub' X = sub).

  Note that in both theorems, `typeinf env fv1 e (fv2, S, C, X)` just means applying constraint typing on `e` produces some `S` and `C`. It doesn't mean `S` and `C` are solvable. To state that these two are solvable, propositions `satisfy sub C` and `app_sub_to_type sub S = T` must be added.

# V. Approach:

  The approach to prove both theorems is to use induction and case analysis on the expression `e`. Doing this divides the proofs into subgoals where each subgoal corresponds to a different case of `e`. Thus, a "divide and conquer" approach was used to tackle a few cases at a time to move towards the completion of a full proof.

  The key to proving Soundness is to recognize that if a substitution satisfies a constraint set, it also satisfies subsets. Knowing this makes it possible to prove sub-expressions of `e` also type check under a type checker.

  The key to proving Completeness is to construct a new substitution that meets all the stated goals. This is trickier and less obvious than Soundness because merging two arbitrary substitutions that satisfy their own constraint set does not necessarily satisfy the union of two sets. Regardless, the intuition for constructing a new substitution is build an extension of sub-substitutions extracted from applying inductive hypotheses on sub-expressions of `e`. Additional lemmas and utility methods on substitutions are obviously required.

# VI. Results:

  Both theorems take efforts to prove. In my experience, Soundness is slightly easier to prove.

  For Soundness, it has been proven successfully and completely. For Completeness, only `ENum`, `EBool`, `EVar`, `ENil`, and `EFun` cases have been proven. `ENum`, `EBool`, `EVar`, and `ENil` cases are easy to prove since they produce no constraints so any existing substitution could easily satisfy the goals. `EFun` case is slightly more difficult. However, since it produces only one constraint set, it is not too difficulty to find a satisfactory substitution -- in this case, the substitution extracted from apply inductive hypothesis on the body of the function.

  Other cases for Completeness are trickier to prove because they involves more than one constraint sets, extracted from sub-expressions. Unfortunately, I ran out of time to work on these cases but I had asked for help and consulted the Completeness proof in _Types and Programming Languages_ book. I had also proved additional lemmas, such as:

  * `typeinf_disjoint_Xs`: `typeinf` introduces distinct new type variables.
  * `app_sub_type_omit_disjoint_list`: if a type variable list do not contain any type variable appears in a type, then remove the type variables in that list from a substitution does not change how it is applied on a type.

  and introduced additional methods on substitutions (which are just `partial_map`s):

  * `take m l`: creates a new partial map from `m` with only the keys in `l`.
  * `omit m l`: creates a new partial map from `m` except the keys in `l`.
  * `merge m1 m2`: merges two maps `m1` and `m2`, with `m2` overriding `m1` if they both have some common keys.

  With these definitions, constructing a new substitution `sub'` for case `ECall` as below:

      sub' =
        (update
          (merge
            (omit sub (e_X ++ f_X ++ [Id e_fv]))
            (merge
              (take subf f_X)   (* subf from applying inductive hypothesis on f *)
              (take sube e_X))) (* sube from applying inductive hypothesis on e *)
          (Id e_fv)
          T)

  should satisfy the goals. From inductive hypotheses, `omit subf f_X = sub` and `omit sube e_x = sub`. From `typeinf_disjoint_Xs` lemma, `f_X` and `e_X` are disjoint. From how `e_fv` is chosen, `Id e_fv` is also distinct from `f_X` and `e_X`. Hence, `sub'` should form a _complete_ substitution where `omit sub (e_X ++ f_X ++ [Id e_fv])` makes up for everything that is missing from merging `take subf f_X` and `take sube e_X`. Then `sub'` should satisfy `e_C ++ f_C`, solving the "tricky" problem discussed in previous section.

  This is the direction for proving `ECall` case. The remaining cases could be proven using a similar approach.

# VII. Lessons Learned:

### About Engineering Proofs:

  * There are tradeoffs between implementation using computable functions or inductive propositions. Using functions are more suitable if I want to compile code into executables whereas using inductive propositions is more suitable for proving the essence of some algorithm because inductive propositions abstract implementation details away. Using recursive functions could be troublesome in some cases because Coq must be convinced the functions terminate properly; and it's not easy to do so. Using functions could make interesting properties about the implementation harder to see (and these properties have to be extracted by proving additional lemmas) whereas using inductive propositions allow those properties to be stated explicitly. For example, if `typeinf` was implemented as a function, I must prove that the implementation produces disjoint `X`s for sub-expressions whereas with inductive propositions, I could state explicitly that the `X`s must be disjoint.

  * Expanding on this point, it is easy to see the current implementation of `typeinf` is not abstract enough. Note that `typeinf` uses those `fv`s to instantiate new type variables and make sure they are distinct. This is an implementation detail because there are many ways to ensure new type variables are distinct, not necessarily with just using `nat`, which is the type of `fv`s. I could have removed those `fv`s and explicitly stated a proposition that asserts new type variables must be distinct and skipped proving that `typeinf` produces distinct type variables, like I did with proving `typeinf_disjoint_Xs` lemma. For example, the typing rules for `ECall` could have been written as below:

        Inductive typeinf : t_env -> t_expr -> (t_type * constr * list id) % type -> Prop :=
          ...
          | TI_Call:
            forall env fv i
              f f_fv f_C f_T f_X
              e e_fv e_C e_T e_X,
            typeinf env f (f_T, f_C, f_X) ->
            typeinf env e (e_T, e_C, e_X) ->
            (~ In i f_X) /\ (~ In i e_X) -> (* explicitly state i must be new, avoiding proving `typeinf_disjoint_Xs` *)
            typeinf env (ECall f e) (TVar i, e_C ++ f_C ++ [(f_T, TFun e_T (TVar i))], e_X ++ f_X ++ [i])

  * Proofs in general seem to be fragile and dependent on implementation. If a program changes its implementation, then proofs about its properties must also be changed. Sometimes the changes could be so drastic that existsing proofs must be discarded and replaced by new proofs. This is not attractive as hours of proof efforts went to waste. Consequently, the implementation must be done perfectly correct first to avoid changing proofs later. This makes it hard to change and experiment with different implementations.

### About Coq as a Tool:

  * Coq is not a practical tool for mainstream software engineering use yet. I take this course in hopes that I could learn to use Coq in daily software development to verify program correctness. I was interested to find out if instead of writing unit tests, I could use Coq to provide a much stronger guarantee about a program property. However, I learned that using Coq is not as easy as it sounds:

    + Coq users must have strong theoretical background to build correct implementation and proofs.
    + Coq users must also know how to navigate the obscure Coq documentation, which often lacks examples and explanation on how a particular tactic is used. For example, if I want to transform a hypothesis in a certain way, there is no easy way for me to search for an appropriate tactic, except going through the tactic index, which says nothing about how a tactic could be used. Instead of simply listing all tactics, organizing them into separate sections or purposes would be perhaps more helpful.
    + CoqIDE and standard library are not sufficiently developed to ease the development of Coq proofs and implementation. CoqIDE is just a pretty Coq text editor that can compile and run Coq programs. It should have more features, such as showing subgoals and hypotheses beforehand or automatically eliminate contradictory cases. Or at least there should be a concise tatic in the standard library to eliminate cases such as `n < n` without writing more than one lines of proof. Additionaly, the standard library should have more tactics that speed up the extraction of subgoals, such as an advanced version of `split` that works for n-ary conjunctions, like `splits` in `LibTactics.v` from _Software Foundations_ book.
    + Coq is already used to verify new algorithms or programs developed from scratch by developing them in Galina, proving their properties, and compiling their implementation to verified executables. However, it is unclear how Coq could be used in the opposite direction: verifying existing programs already developed in different languages. This approach is more complicated because it's hard to formalize a translation of program behaviors to Coq that preserves semantics. It appears that an abstracted, distilled version of the program must be used in Coq proofs to simplify complexity. Then, however, it is hard to convince these proofs are any useful given how they only prove program properties so abstract that they dissociate from actual implementation. Given how many existing programs there are and how people are more interested in improving or fixing existing software, using Coq to verify existing programs is not practical.

  * Despite high learning curve, Coq is very useful for students looking for hands-on experience with theoretical concepts. Everyone probably agrees the best way to learn is by doing. This principle also applies for learning theoretical concepts. Going to lectures and doing homework probably won't make one understand a concept as well as implementing it and proving it in Coq. Only by trying to prove the concept does one then know its nuances and subtleties, or at least this is the case for me. Before doing this project, I had some idea (even incorrect) about constraint typing and type inference and didn't fully know every details. However, after seeing my Coq implementation "crash and burn", revising my implementation many times, and struggling to understand why some cases are unprovable, I have a much better understanding constraint typing rules and the two theorems.
