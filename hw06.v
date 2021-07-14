From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive expr : Type :=
| Const of nat
| Plus of expr & expr
| Minus of expr & expr
| Mult of expr & expr
.
Print expr.


Declare Custom Entry expr.

Notation "'[[' e ']]'" := e (e custom expr at level 0).

Notation "x" :=
  (Const x)
    (in custom expr at level 0, x bigint).

Notation "( x )" := x (in custom expr, x at level 2).
Notation "x + y" := (Plus x y) (in custom expr at level 2, left associativity).

Notation "x - y" := (Minus x y) (in custom expr at level 2).
Notation "x * y" := (Mult x y) (in custom expr at level 1).

Check [[
          0 + (1 + 2)
      ]].
Check [[
          (0 + 1) + 2
      ]].

Check [[
          ((0 + 1) + 2) + 3
      ]].
Check [[
          0 + (1 + (2 + 3))
      ]].
Check [[
          0 * 1 + 2
      ]].
Check [[
          0 + 1 * 2
      ]].

Fixpoint eval (e : expr) : nat :=
  match e with
  | Const x => x
  | Plus x y => eval x + eval y
  | Minus x y => eval x - eval y
  | Mult x y => eval x * eval y
  end.

(** Some unit tests *)
Check erefl : eval [[ 0 - 4 ]] = 0.
Check erefl : eval [[ 0 + (2 - 1) ]] = 1.
Check erefl : eval [[ (0 + 1) + 2 ]] = 3.
Check erefl : eval [[ 2 + 2 * 2 ]] = 6.
Check erefl : eval [[ (2 + 2) * 2 ]] = 8.
Fail Check erefl : eval [[ 0 + 7 ]] = 4.
Compute eval [[3 + 30]].

(** * Compiling arithmetic expressions to a stack language *)

Inductive instr := Push (n : nat) | Add | Sub | Mul.

Notation " << n >> " := (Push n) (at level 0, n constr).

Definition prog := seq instr.
Definition stack := seq nat.


(** The [run] function is an interpreter for the stack language. It takes a
 program (list of instructions) and the current stack, and processes the program
 instruction-by-instruction, returning the final stack. *)
Definition run_step (s : stack) (p : instr) : stack :=
  match p with
  | Push n => n :: s
  | Add => if s is x::y::s' then ((y + x) :: s') else s 
  | Sub => if s is x::y::s' then ((y - x) :: s') else s 
  | Mul => if s is x::y::s' then ((y * x) :: s') else s 
  end.

Print foldl.
Definition run (p : prog) (s : stack) : stack :=
  foldl run_step s p. 
(** Unit tests: *)
Check erefl : run [:: (Push 4)] [::] = [:: 4].
Check erefl : run [:: (Push 4) ; (Push 3) ; Add] [::] = [:: 7].
Check erefl : run [:: (Push 3) ; (Push 4) ; Sub] [::] = [:: 0].
Check erefl : run [:: (Push 4) ; (Push 3) ; Mul] [::] = [:: 12].
Check erefl : run [:: (Push 8) ; (Push 2) ; Sub] [::] = [:: 6].



Fixpoint compile (e : expr) : prog :=
  match e with
  | Const x => [:: (Push x)]
  | Plus x y => compile x ++ compile y ++ [:: Add]
  | Minus x y => compile x ++ compile y ++ [:: Sub]
  | Mult x y => compile x ++ compile y ++ [:: Mul]
  end.



Lemma run_part xs ys s :
  run (xs ++ ys) s = run ys (run xs s).
Proof.
elim: xs ys s=> [// | i xs IHyp] ys s ; by rewrite /=.
Qed.

Theorem compile_correct' e s :
  run (compile e) s = [:: eval e] ++ s.
Proof.
elim: e s=> // e ihe b ihb /= s ; by rewrite !run_part ihe ihb /=.
Qed.
 

(** Here is a correctness theorem for the compiler: it preserves the
meaning of programs. By "meaning", in this case, we just mean the final
answer computed by the program. For a high-level expression, the answer
is the result of calling [eval]. For stack programs, the answer
is whatever [run] leaves on the top of the stack. The correctness
theorem states that these answers are the same for an expression and
the corresponding compiled program. *)
Theorem compile_correct e :
  run (compile e) [::] = [:: eval e].
Proof.
exact: compile_correct' e [::].
Qed.


(* ==== OPTIONAL part: decompiler ==== *)

Fixpoint decompile' (p : prog) (acc : seq expr) : seq expr :=
  if p is (i :: p') then
    let acc' :=
        match i with
        | Push n => Const n :: acc
        | Add => if acc is (e1 :: e2 :: acc') then Plus e2 e1 :: acc'
                 else acc
        | Sub => if acc is (e1 :: e2 :: acc') then Minus e2 e1 :: acc'
                 else acc
        end
    in
    decompile' p' acc'
  else acc.

(** return a default value for the empty program *)
Definition decompile (p : prog) : option expr :=
  if decompile' p [::] is [:: result] then some result
  else None.
Arguments decompile p / : simpl nomatch.


Definition decompile (p : prog) : option expr :=
  replace_with_your_solution_here.

(** Prove [decompile] cancels [compile]. *)
Lemma decompile_compile e :
  decompile (compile e) = Some e.
Proof.
Admitted.

(* Prove the [compile] function is injective *)
Lemma compile_inj :
  injective compile.
Proof.
Admitted.