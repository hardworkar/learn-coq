From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Lemma addnC :
    commutative addn.
Proof.
move=> x y.
elim: x.
- rewrite add0n.
elim: y=> // y IHy.
rewrite addSn -IHy.
done.
Restart.
elim=> [| x IHx] y; first by rewrite addn0.
by rewrite addSn IHx addnS.
Qed.

Locate "`!".
Print factorial.
Print fact_rec.

Fixpoint factorial_helper (n : nat) (acc : nat) : nat :=
    if n is n'.+1 then
        factorial_helper n' (n * acc)
    else
        acc.
Definition factorial_iter (n : nat) : nat :=
    factorial_helper n 1.

Lemma factorial_iter_correct n :
    factorial_iter n = n`!.
Proof.
elim: n.
- done.
move=> n IHn.
rewrite /factorial_iter.
move=> /=.
rewrite muln1.
rewrite /factorial_iter in IHn.
Abort.

Lemma factorial_helper_correct n acc :
    factorial_helper n acc = n`! * acc.
Proof.
elim: n=> [| n IHn /=]; first by rewrite fact0 mul1n.
Restart.
move: acc.
elim: n.
- move=> acc.
  by rewrite fact0 mul1n.
move=> n IHn acc /=.
rewrite IHn.
by rewrite factS mulnCA mulnA.

Restart.
elim: n acc=> [| n IHn /=] acc; first by rewrite fact0 mul1n.
by rewrite IHn factS mulnCA mulnA.
Qed.

Lemma factorial_iter_correct n :
    factorial_iter n = n`!.
Proof.
rewrite /factorial_iter.
by rewrite factorial_helper_correct muln1.
Qed.

Search _ left_id muln.

(* Custom Induction Principles *)
Fail Fixpoint fib (n : nat) : nat :=
    if n is n''+2 then
        fib n'' + fib n''.+1
    else n.

Fixpoint fib (n : nat) : nat :=
    if n is (n''.+1 as n').+1 then
        fib n'' + fib n'
    else n.

Section Illustrate_simpl_nomatch.
Variable n : nat.
Lemma default_behavior :
    fib n.+2 = 0.
Proof.
move=> /=.
Abort.

Arguments fib n : simpl nomatch.

Lemma after_simpl_nomatch :
    fib n.+2 = 0.
Proof.
move=> /=.
Abort.
End Illustrate_simpl_nomatch.

Fixpoint fib_iter (n : nat) (f0 f1 : nat) : nat :=
    if n is n'.+1 then
        fib_iter n' f1 (f0 + f1)
    else f0.
Arguments fib_iter n f0 f1 : simpl nomatch.

Lemma fib_iterS n f0 f1 :
    fib_iter n.+1 f0 f1 = fib_iter n f1 (f0 + f1).
Proof. by []. Qed.

Lemma fib_iter_sum n f0 f1 :
    fib_iter n.+2 f0 f1 =
    fib_iter n f0 f1 + fib_iter n.+1 f0 f1.
Proof.
elim: n f0 f1 => [// | n IHn] f0 f1.
rewrite fib_iterS.
rewrite IHn.
done.
Qed.

Arguments fib n : simpl nomatch.

Lemma fib_iter_correct n :
    fib_iter n 0 1 = fib n.
Proof.
elim: n=> //= n IHn. 
Abort.

Lemma nat_ind2 (P : nat -> Prop) :
    P 0 ->
    P 1 ->
    (forall n, P n -> P n.+1 -> P n.+2) ->
    forall n, P n.
Proof.
move=> p0 p1 Istep n.
have: P n /\ P n.+1.
- elim: n=> // n [IHn IHSn].
  split=> //.
  by apply: Istep.
by case.

Restart.

move=> p0 p1 Istep n; suff: P n /\ P n.+1 by case.
elim: n=> // n [IHn IHSn] . split=> //; exact: Istep.

Restart.
move=> p0 p1 Istep n; suff: P n /\ P n.+1 by case.
by elim: n=> // n [/Istep pn12] /[dup]/pn12.

Restart.
move=> p0 p1 Istep n; suff: P n /\ P n.+1 by case.
elim: n=> // n.
case.
move/Istep.
move=> pn12.
move=> /[dup].
move=> /pn12.
done.
Qed.

Lemma fib_iter_correct n :
    fib_iter n 0 1 = fib n.
Proof.
elim/nat_ind2: n => // n IHn1 IHn2.
by rewrite fib_iter_sum IHn1 IHn2.
Qed.

(* Complete induction *)
Lemma fib_iter_correct' n :
    fib_iter n 0 1 = fib n.
Proof.
elim/ltn_ind: n=> n IHn.
case: n IHn => // n IHn.
case: n IHn => // n IHn.
rewrite fib_iter_sum.
rewrite !IHn ; done.

Restart.
elim/ltn_ind: n=> [] // [] // [] // n IHn.
by rewrite fib_iter_sum !IHn.

Qed.

