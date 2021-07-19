(* Canonical structures & hierarchies *)
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq bigop.

Import Monoid.
Print Monoid.Law.
Print Canonical Projections operator.
About mulmA.
Lemma foo m n p q r :
    m + (n + p * (q * r)) = m + n + p * q * r.
Proof.
by rewrite !mulmA /=.
Qed.