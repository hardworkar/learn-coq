From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* SSReflect tactic practice *)

Section IntLogic.

Variables A B C : Prop.

(** * Exercise *)
Lemma andA :
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
case.
case.
move=> a b c.
split.
- exact: a.
split.
- exact: b.
exact: c.

Restart.
by case=> [[a b] c].
Qed.

Lemma andA' :
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
by case=> [[a b] c].
Defined.

About andA.

Compute andA.

About andA'.

Compute andA'.


(** * Exercise *)
Lemma conj_disjD :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
by case=> [a [b | c]] ; [left | right].
Qed.


(** * Exercise *)
Lemma disj_conjD :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
by case=> [a | [b c]]; [split; left | split ; right].
Qed.


(** * Exercise *)
Lemma notTrue_iff_False :
  (~ True) <-> False.
Proof.
split ; [by apply | case].
Qed.
(** Hint 1: use [case] tactic on a proof of [False] to apply the explosion
principle. *)
(** Hint 2: to solve the goal of the form [True], use [exact: I], or simple
automation. *)


(** * Exercise *)

Lemma imp_trans :
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
move=> ab bc a.
apply: bc.
by apply: ab.
Restart.
by move=> ab bc /ab.
Qed.


(** * Exercise *)
Lemma dne_False :
  ~ ~ False -> False.
Proof.
by apply.
Qed.

(** * Exercise *)
Lemma dne_True :
  ~ ~ True -> True.
Proof.
move=> _.
exact: I.
Qed.



(** * Exercise *)
Lemma LEMisNotFalse :
  ~ ~ (A \/ ~ A).
Proof.
rewrite /not.
move=> nlem.
apply: (nlem).
right => a.
apply: (nlem).
by left.
Qed.
(** Hint : use `apply: (identifier)`
to apply a hypothesis from the context to
the goal and keep the hypothesis in the context *)


(** * Exercise *)
Lemma weak_Peirce :
  ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
move=> f1.
apply (f1).
move=> f2.
apply (f2).
move=> a.
apply f1.
move=> _.
done.
Qed.

End IntLogic.


Section EquationalReasoning.

Variables A B : Type.

(** * Exercise 10 *)
Lemma eqext_refl (f : A -> B) :
  f =1 f.
Proof.
move=> x.
done.
Qed.


(** * Exercise 11 *)
Lemma eqext_sym (f g : A -> B) :
  f =1 g -> g =1 f.
Proof.
move=> fg ?.
by rewrite fg.
Qed.

(** Hint: `rewrite` tactic also works with
universally quantified equalities. I.e. if you
have a hypothesis `eq` of type `forall x, f x = g
x`, you can use `rewrite eq` and Coq will usually
figure out the concrete `x` it needs to specialize
`eq` with, meaning that `rewrite eq` is
essentially `rewrite (eq t)` here. *)


(** * Exercise *)
Lemma eqext_trans (f g h : A -> B) :
  f =1 g -> g =1 h -> f =1 h.
Proof.
move=> fg gh ?.
rewrite fg.
by rewrite -gh.
Qed.

End EquationalReasoning.



(** * Exercise *)
Lemma and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B.
Proof.
split.
- case.
  done.
case.
move=> a b.
split ; done.
Qed.


(** * Exercise *)
(* Hint: the `case` tactic understands constructors are injective *)
Lemma pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
Proof.
by case.
Qed.


(** * Exercise *)
Lemma false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False.
Proof.
Admitted.


(** * Exercise *)
Lemma addn0 :
right_id 0 addn.
Proof.
rewrite /right_id.
elim.
- done.
move=> n IHn.
by rewrite addSn IHn.
Qed.


(** * Exercise *)
Lemma addnS :
  forall m n, m + n.+1 = (m + n).+1.
Proof.
move=> m n.
elim: m.
done.
move=> m IHm.
rewrite addSn IHm addSn.
done.
Qed.


(** * Exercise: *)
Lemma addnCA : left_commutative addn.
Proof.
rewrite /left_commutative.
move=> x y z.
elim: x.
done.
move=> x IHx.
by rewrite addSn IHx -addnS addSn.
Qed.


(** * Exercise: *)
Lemma addnC : commutative addn.
Proof.
rewrite /commutative.
move=> x y.
rewrite -(addn0 (x + y)).
rewrite -(addn0 (y + x)).
rewrite -addnA.
rewrite addnCA.
rewrite addnA.
done.

(** * Exercise (optional): *)
Lemma unit_neq_bool:
  unit <> bool.
Proof.

Admitted.