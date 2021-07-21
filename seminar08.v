From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path order.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Insertion.
Section InsertionSort.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.
Implicit Types s t u : seq T.

(*| Insert an element `e` into a sorted list `s` |*)
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

(** * Exercise *)
Lemma sorted_cons x s :
  sorted leT (x :: s) -> sorted leT s.
Proof.
by move=> //= ; case: s=> //= e y /andP[].
Qed.


Hypothesis leT_total : total leT.
Lemma insert_sorted x s :
    sorted leT s ->
    sorted leT (insert x s).
Proof.
elim: s=> //= e s IHs.
case: ifP=> /= [->-> // | ].
move=> le_x_e_false path_e_s.
have:= leT_total x e.
rewrite le_x_e_false /=.
move=> le_e_x.
move: path_e_s=> {}/path_sorted/IHs.
case: s=> //= ; first by rewrite le_e_x.
Admitted.

(** * Exercise *)
Lemma sort_sorted s :
  sorted leT (sort s).
Proof.
elim: s=> //= x s IHs.
by rewrite insert_sorted.
Qed.

End InsertionSort.
End Insertion.



(** * Exercise: implement guarded interleave function *)

(* here is its unguarded version *)
Unset Guard Checking.
Fixpoint interleave_ns {T} (xs ys : seq T)
           {struct xs} : seq T :=
  if xs is (x :: xs')
  then x :: interleave_ns ys xs'
  else ys.
Set Guard Checking.

(** A simple unit test. *)
Check erefl : interleave_ns [:: 1; 3] [:: 2; 4] = [:: 1; 2; 3; 4].

Fixpoint interleave {T} (xs ys : seq T) : seq T :=
    match xs, ys with
    | [::], _ => ys
    | _, [::] => xs
    | x::xs', y::ys' => x :: y :: interleave xs' ys'
    end.
Check erefl : interleave [:: 1; 3] [:: 2; 4] = [:: 1; 2; 3; 4].

Lemma interleave_ns_eq_interleave {T} :
  (@interleave_ns T) =2 (@interleave T).
Proof. by elim=> // x xs IHs [] // y ys /= ; rewrite IHs.
Qed.


(** * Exercise: implement Ackermann's function

It's defined via the following expressions:

  A(0,   n)   = n + 1
  A(m+1, 0)   = A(m, 1)
  A(m+1, n+1) = A(m, A(m+1, n))
*)
Fixpoint acker m n :=
    let fix acker_m n :=
    match m, n with
    | O, _ => n + 1
    | S m', O => acker m' 1
    | S m', S n' => acker m' (acker_m n')
    end
    in acker_m n.
Check erefl : acker 0 0 = 1.
Check erefl : acker 0 1 = 2.
Check erefl : acker 1 0 = 2.
Check erefl : acker 1 1 = 3.
Check erefl : acker 3 2 = 29.
Check erefl : acker 4 0 = 13.



(** * Exercise: implement merge function via Program plugin *)
From Coq Require Import Program.
Program Fixpoint merge2 s t {measure (size s + size t)} : seq nat :=
    match s, t with
    | [::], _ => t
    | _, [::] => s
    | x :: s', y :: t' =>
        if (x <= y)%O
        then x :: merge2 s' t
        else y :: merge2 s t'
    end.
Next Obligation.
apply/ltP ; move=> //=; by rewrite ltn_add2l ltnSn.
Qed.
Compute merge2 [::] [::].
Compute merge2 [:: 1; 2; 3] [::].
Compute merge2 [:: 1; 2; 3] [:: 1; 2; 3].
Compute merge2 [::] [:: 1; 2; 3].
Compute merge2 [:: 1; 4; 6] [:: 1; 2; 3].