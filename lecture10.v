From Equations Require Import Equations.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
(* From mathcomp Require Import zify. *)

Set Equations Transparent.

(* Equations plugin *)
Equations fib (n : nat) : nat :=
    fib 0 := 0;
    fib n'.+1 with n' :=
        fib n'.+1 n''.+1 := fib n'' + fib n';
        fib n'.+1 0 := 1.

Equations fib_iter (n : nat) (f0 f1 : nat) : nat :=
    fib_iter n'.+1 f0 f1 := fib_iter n' f1 (f0 + f1);
    fib_iter 0 f0 f1 := f0.

Compute fib 5.

(* lia skipped *)

(* Functional induction *)
Lemma fib_iter_correct n :
    fib_iter n 0 1 = fib n.
Proof.
apply: (fib_elim (fun n f => fib_iter n 0 1 = f)) => //.
move=> {} n n' IH1 IH2 n_eq_Sn'.
rewrite n_eq_Sn' in IH2.
Admitted.

(* CoqHammer package *)
(* Skipped *)

From QuickChick Require Import QuickChick.
Import QcDefaultNotation.
Open Scope qc_scope.
Import GenLow GenHigh.

Set Warnings "-extraction-opaque-sccessed,-extraction".

Inductive instr := Push (n : nat) | Add | Sub | Mul.

(*|
Extraction
========== |*)

From Coq Require Import Extraction.

Module Insertion.
Section InsertionSort.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.
Implicit Types s t u : seq T.
Fixpoint insert e s : seq T :=
  if s is x :: s' then
    if leT e x then
      e :: s
    else
      x :: (insert e s')
  else [:: e].

(*| Sort input list `s` |*)
Fixpoint sort s : seq T :=
  if s is x :: s' then
    insert x (sort s')
  else
    [::].

(*| Proofs of correctness skipped |*)

End InsertionSort.

Extraction Language OCaml.
Extraction sort.


Extraction Language Haskell.
Extraction sort.


(*| Caveat: extracting SSReflect-based projects is
usually not straightforward. It can be done, see
e.g. https://github.com/certichain/toychain. But
one has to overcome some issues. |*)

End Insertion.
