(* Views. reflect-predicate. Multi-rewrite rules *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* reflect-predicate *)
Lemma all_filter T (p : pred T) (s : seq T) :
    all p s -> filter p s = s.
Proof.
Print pred.
Check all.
Locate "[ 'seq' x <- s | C ]".
Print filter.
Check all p s : bool.
Check all p s : Type. (* implicit coercions *)

Set Printing Coercions.
Print is_true.
Locate "^~".
rewrite /is_true.
Unset Printing Coercions.
elim: s=> //= x s IHs.
move=> /andP.
case.
move=> ->.
move /IHs.
move=> ->.
done.

Restart.
by elim: s=> //= x s IHs /andP [-> /IHs ->].
Qed.

About andP.
Print reflect.
Print Bool.reflect.

Goal forall P, reflect P true -> P.
move=> P.
exact: (
    fun r : reflect P true =>
        ((match
            r in reflect _ b
            return (b = true -> P)
        with
        | ReflectT p => fun E => p
        | ReflectF np => fun E => ltac:(done)
        end) erefl)
).
Undo.
case.
Undo.

move=> R.

case E: true / R.
- done.
done.

Restart.
by move=> R; case E: true /.

Restart.
by move=> P; case E: _ /.
Qed.

Lemma introT_by (P : Prop) (b : bool) :
    reflect P b -> (P -> b).
Proof.
case.
done.
by move=> /[apply].
(* by move=> nP /nP. *)
Qed.

Lemma elimT_my (P : Prop) (b : bool) :
    reflect P b -> (b -> P).
Proof.
case=> //.
Qed.
(* Connection of P and b *)
Lemma reflect_property (P : Prop) (b : bool) :
    reflect P b -> (P <-> b).
Proof.
by split ; [apply introT_by | apply elimT_my].
Qed.

Lemma reflect_lem P b :
    reflect P b -> P \/ ~ P.
Proof.
move /reflect_property.
case: b; move=> pp.
by left ; apply pp.
by right=> /pp.
Qed.

Lemma andP_my (b c : bool) :
    reflect (b /\ c) (b && c).
Proof.
case: b.
- case: c.
  - by apply ReflectT.
constructor.
by case.
case: c.
constructor.
by case.
constructor.
by case.

Restart.
by case: b; case: c; constructor=> // ; case.
Qed.

Lemma nandP_my b c :
    reflect (~~ b \/ ~~ c) (~~ (b && c)).
case b; case c; constructor.
by case.
by right.
by left.
by left.

Restart.
by case: b; case c; constructor; intuition.

Qed.

Lemma idP_my (b : bool) :
    reflect b b.
by case: b; constructor.
Qed.


Lemma special_support_for_reflect_predicates b c :
    b && c -> b /\ c.
Proof.
move /andP.
Show Proof.
About elimTF.
Restart.
move=> Hb.
Check @elimTF (b /\ c) (b && c) true (@andP b c) Hb.
move: Hb.
move /(@elimTF (b /\ c) (b && c) true (@andP b c)).
exact: id.

Restart.
move=> Hb.
exact: elimT_my andP Hb.


Qed.

Lemma special_support_for_reflect_predicates' b c :
    (b && c) = false -> ~ (b /\ c).
Proof.
move/andP.
Restart.
move=> Hb.
Check @elimTF (b /\ c) (b && c) false (@andP b c) Hb.
exact: @elimTF (b /\ c) (b && c) false (@andP b c) Hb.
Qed.


Lemma special_support_for_reflect_predicates'' (b c : bool) :
    b /\ c -> b && c.
Proof.
move=> /andP.
Show Proof.
About introT.
Restart.
move=> Hb.
exact: @introT (b /\ c) (b && c) (@andP b c) Hb. 
Qed.


Lemma special_support_for_reflect_predicates''' (b c : bool) :
    b /\ c -> b && c.
Proof.
move=> bc.
apply/andP.
done.
Qed.

Lemma special_support_for_reflect_predicates'''' (b c : bool) :
    ~ (b /\ c) -> b && c = false.
Proof.
move=> ab.
apply/andP.
done.
Qed.

Lemma eqnP_my (n m : nat) :
    reflect (n = m) (eqn n m).
Proof.
apply: (iffP idP).
by elim: n m => [| n IHn] [|m] //= /IHn ->.
by move=> -> ; elim: m.
Qed.

Lemma nseqP (T : eqType) n (x y : T) :
    reflect (y = x /\ n > 0) (y \in nseq n x).
Proof.
rewrite mem_nseq.
rewrite andbC.
apply: (iffP andP).
case.
by move/eqP.
by case=> ->.

Restart.
by rewrite mem_nseq andbC ; apply: (iffP andP) => [[/eqP] | [/eqP]].

Restart.
by rewrite mem_nseq andbC ; apply: (iffP andP) => -[/eqP].
Qed.

About maxn_idPl.
Lemma leq_max m n1 n2 :
    (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
without loss le_n21: n1 n2 / n2 <= n1.
by case/orP : (leq_total n2 n1) => le ; last rewrite maxnC orbC ; apply.
rewrite (maxn_idPl le_n21).
Search leq.
case: ltngtP=> _ //.

case/orP.
Admitted.


About allP.

Example for_ltngtP m n :
    (m <= n) && (n <= m) ->
    (m == n) || (m > n) || (m + n == 0).
by case: ltngtP.    
About ltngtP.
About compare_nat.

Restart.
case: ltngtP => //.
Qed.


Variant compare_nat m n :
    bool -> bool -> bool -> bool -> bool -> bool -> Type :=
| CompareNatLt of m < n :
    compare_nat m n false false false true false true
| CompareNatGt of m > n :
    compare_nat m n false false true false true false
| CompareNatEq of m = n :
    compare_nat m n true true true true false false.


Lemma ltngtP m n :
    compare_nat m n (n == m) (m == n) (n <= m)
                    (m <= n) (n < m) (m < n).
Proof.
Admitted.