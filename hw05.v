From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Use SSReflect tactics.
    DO NOT use automation like [tauto], [intuition], [firstorder], etc.,
    except for [by], [done], [exact] tactic(al)s. *)


(** * Exercise *)
Lemma nlem (A : Prop):
  ~ (A \/ ~ A) -> A.
Proof.
rewrite /not.
move=> f.
move: (f).
case.
right.
move=> a.
apply f.
left.
done.
Qed.

(** Hint: you might want to use a separate lemma here to make progress.
Or, use the `have` tactic: `have: statement` creates a new subgoal and asks
you to prove the statement. This is like a local lemma. *)


(** * Exercise *)
Lemma weak_Peirce (A B : Prop) :
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



(** * Exercise *)
(* Prove that having a general fixed-point combinator in Coq would be incosistent *)
Definition FIX := forall A : Type, (A -> A) -> A.

Lemma fix_inconsistent :
  FIX -> False.
Proof.
rewrite /FIX.
apply.
done.
Qed.


Section Boolean.
(** * Exercise *)
Lemma negbNE b : ~~ ~~ b -> b.
Proof.
by case: b ; done.
Qed.


(** * Exercise *)
Lemma negbK : involutive negb.
Proof.
rewrite /involutive /cancel.
move=> x.
by case: x ; done.
Qed.


(** * Exercise *)
Lemma negb_inj : injective negb.
Proof.
rewrite /injective.
move=> x1 x2.
by case: x1 ; case: x2 ; done.
Qed.

End Boolean.


(** * Exercise *)
Fixpoint triple (n : nat) : nat :=
  if n is n'.+1 then (triple n').+3
  else n.

Lemma triple_mul3 n :
  triple n = 3 * n.
Proof.
elim: n.
done.
move=> n IHn.
move=> /=.
rewrite mulnS -IHn.
done.
Qed.
(** Hints:
- use the /= action to simplify your goal: e.g. move=> /=.
- use `Search (<pattern>)` to find a useful lemma about multiplication
*)

Lemma dummy m n :
    m = n.+1 -> m.-1 = n.
Proof.
move=> ->.
done.
Qed.

Lemma dummy2 m :
  (m + m).-1 = m + m.-1.
Proof.
elim: m.
done.
move=> n IHn.
rewrite addnS addSn.
done.
Qed.
Lemma dummy3 m n:
  m > 0 -> (m + n).-1 = m.-1 + n.
Proof.
elim: n.
by rewrite addn0 addn0.
move=> n IHn.
move=> gtHyp.

rewrite addnS addnS.
rewrite -(IHn gtHyp) -pred_Sn.
rewrite prednK.
done.
exact: ltn_addr n gtHyp.
Qed.
Lemma idk_how_to_find_it_so (b : bool) :
  (b || b) -> b.
Proof. case: b ; done. Qed.
(** * Exercise
Prove by it induction: you may re-use the addnS and addSn lemmas only *)
Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.
move: n.
elim: m.
move=> n.
case: n; done.
move=> n IHm m.

rewrite addnS.
move=> H1.
move: (H1).
move=> _.
move: (dummy (Logic.eq_sym H1)).
rewrite dummy2.

rewrite addSn.
move=> H2.
move: (H2).
move=> _.
move: (dummy H2).
rewrite dummy3.
move=> Hyp.
move: (congr1 S (IHm m.-1 (Logic.eq_sym Hyp))).

rewrite prednK.
done.

(* Yep they are the same. idk how to fix that for now *)
move: H1.
move: (ltn0Sn ((n.+1 + n))).
move=> gtHyp eqnm.
rewrite eqnm in gtHyp.
rewrite (addn_gt0 m m) in gtHyp.
exact: (idk_how_to_find_it_so gtHyp).

move: H1.
move: (ltn0Sn ((n.+1 + n))).
move=> gtHyp eqnm.
rewrite eqnm in gtHyp.
rewrite (addn_gt0 m m) in gtHyp.
move: (idk_how_to_find_it_so gtHyp).
done.
Qed.
(* This is a harder exercise than the previous ones but
   the tactics you already know are sufficient *)




(** * Optional exercise
    [negb \o odd] means "even".
    The expression here says, informally,
    the sum of two numbers is even if the summands have the same "evenness",
    or, equivalently, "even" is a morphism from [nat] to [bool] with respect
    to addition and equivalence correspondingly.
    Hint: [Unset Printing Notations.] and [rewrite /definition] are your friends :)
 *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Proof.
Admitted.


(** * Optional exercise *)
Lemma DNE_iff_nppp :
  (forall P, ~ ~ P -> P) <-> (forall P, (~ P -> P) -> P).
Proof.
Admitted.


(** * Optional exercise *)
Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Proof.
Search (_ <= _ + _).
Admitted.
(** Hint: this lemmas does not require induction, just look for a couple lemmas *)





(* ================================================ *)

(*
More fun with functions, OPTIONAL
*)

Section PropertiesOfFunctions.

Section SurjectiveEpic.
Context {A B : Type}.

(* https://en.wikipedia.org/wiki/Surjective_function *)
(** Note: This definition is too strong in Coq's setting, see [epic_surj] below *)
Definition surjective (f : A -> B) :=
  exists g : B -> A, f \o g =1 id.

(** This is a category-theoretical counterpart of surjectivity:
    https://en.wikipedia.org/wiki/Epimorphism *)
Definition epic (f : A -> B) :=
  forall C (g1 g2 : B -> C), g1 \o f =1 g2 \o f -> g1 =1 g2.

(** * Optional exercise *)
Lemma surj_epic f : surjective f -> epic f.
Proof.
Admitted.

(** * Optional exercise *)
Lemma epic_surj f : epic f -> surjective f.
  (** Why is this not provable? *)
Abort.

End SurjectiveEpic.


Section EpicProperties.
Context {A B C : Type}.

(** * Optional exercise *)
Lemma epic_comp (f : B -> C) (g : A -> B) :
  epic f -> epic g -> epic (f \o g).
Admitted.

(** * Optional exercise *)
Lemma comp_epicl (f : B -> C) (g : A -> B) :
  epic (f \o g) -> epic f.
Admitted.

(** * Optional exercise *)
Lemma retraction_epic (f : B -> A) (g : A -> B) :
  (f \o g =1 id) -> epic f.
Admitted.

End EpicProperties.


(** The following section treats some properties of injective functions:
    https://en.wikipedia.org/wiki/Injective_function *)

Section InjectiveMonic.

Context {B C : Type}.

(** This is a category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)
Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

(** * Optional exercise *)
Lemma inj_monic f : injective f -> monic f.
Proof.
Admitted.


(** * Optional exercise *)
Lemma monic_inj f : monic f -> injective f.
Proof.
Admitted.

End InjectiveMonic.


Section MonicProperties.
Context {A B C : Type}.

(** * Optional exercise *)
Lemma monic_comp (f : B -> C) (g : A -> B) :
  monic f -> monic g -> monic (f \o g).
Proof.
Admitted.

(** * Optional exercise *)
Lemma comp_monicr (f : B -> C) (g : A -> B) :
  monic (f \o g) -> monic g.
Proof.
Admitted.

(** * Optional exercise *)
Lemma section_monic (f : B -> A) (g : A -> B) :
  (g \o f =1 id) -> monic f.
Proof.
Admitted.

End MonicProperties.

End PropertiesOfFunctions.