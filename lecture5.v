(* The SSReflrect tactic language *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* tactics - metalanguage *)
(* typechecker still works! *)

(* Basic tactics *)
Lemma A_implies_A :
    forall (A : Prop), A -> A.
Proof.
move=> A.
move=> proof_A.
exact: proof_A.
Qed.

Lemma A_implies_A' :
    forall (A : Prop), A -> A.
Proof.
move=> A.
Show Proof.
move=> proof_A.
Show Proof.
exact: proof_A.
Show Proof.
Unset Printing Notations.
Show Proof.
Qed.

Lemma A_implies_B_implies_A (A B : Prop) :
    A -> B -> A.
Proof.
move=> a.
move=> _.
exact: a.
Qed.

Lemma modus_ponens (A B : Prop) :
    A -> (A -> B) -> B.
Proof.
move=> a.
apply. (* backward reasoning *)
(* after this step we need to prove A *)
exact: a.
Qed.

Definition and1 (A B : Prop) :
    A /\ B -> A.
Proof.
case.
move=> a _.
exact: a.
Qed.

Definition andC (A B : Prop) :
    A /\ B -> B /\ A.
Proof.
case.
move=> a b.
(* prove conjunction: creates one more subgoal *)
split.
(* 1st subgoal marked with a bullet and indented *)
- exact: b.
exact: a.
Qed.

Definition orC (A B : Prop) :
    A \/ B -> B \/ A.
Proof.
case.
- move=> a.
    right. (* prove right disjunct *)
    exact: a.
move=> b.
left.
exact: b.
Qed.

Lemma or_and_distr A B C :
    (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
case.
case.
- move=> a c.
    left.
    split.
    - exact: a.
    exact: c.
move=> b c.
right.
split.
- exact: b.
exact: c.
Qed.

Lemma or_and_distr1 A B C :
    (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
case.
case=> [a|b] c.
- by left.
by right.
Qed.

Lemma or_and_distr2 A B C :
    (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof. by case=> [[a|b] c]; [left | right]. Qed.

Lemma HilbertSaxiom A B C :
    (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab a.
move: abc.
apply.
- by [].
move: ab.
apply.
done.
Qed.

Lemma HilbertSaxiom1 A B C :
    (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab a.
apply: abc.
- by [].
by apply: ab.
Qed.

Lemma HilbertSaxiom2 A B C :
    (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab a.
apply: abc=> //.
by apply: ab.
Qed.

(* Rewrite tactic and -> action *)
Section RewriteTactic.

Variable A : Type.
Implicit Types x y z : A.

Lemma esym x y :
    x = y -> y = x.
Proof.
move=> x_eq_y.
rewrite x_eq_y. (* change x to y: from left to right *)
by [].
Qed.

Lemma esym_shorter x y :
    x = y -> y = x.
Proof.
move=> ->.
done.
Qed.

Lemma eq_trans x y z :
    x = y -> y = z -> x = z.
Proof.
move=> ->.
done.
Qed.

End RewriteTactic.

Lemma addnA :
    associative addn.
Proof.
rewrite /associative.
move=> x y z.
Restart.
Show.
move=> x y z.
(* we need induction on x: *)
move: x.
elim.
Show Proof.
by [].
move=> x IHx.
Fail rewrite IHx.
(* To use 'IHx' we need to change the goal
   to contain 'x + (y + z)' *)
(* To achieve this we need some lemma:
   'x.+1 + y' -> '(x+y).+1' *)
Search (_.+1 + _).
rewrite (addSn x (y+z)).
rewrite IHx.
done.
Restart.
by move=> x y z; elim: x=> // x IHx; rewrite addSn IHx.
Qed.