From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Exercise: Define equality type for the following datatype *)
Inductive tri :=
| Yes | No | Maybe.

Print eq_op.
About eq_op.
(* rel T := T -> T -> bool *)
Print Equality.type.
(*
Definition tri_eq : tri -> tri -> bool :=
    fun a b =>
        match a, b with
        | Yes, Yes | No, No | Maybe, Maybe => true
        | _, _ => false
        end.
Lemma tri_eq_proof : Equality.axiom tri_eq.
Proof.
by case; case; constructor.
Qed.

Canonical tri_eqType :=
    EqType tri (EqMixin tri_eq_proof).

Check (1, Yes) == (1, Maybe).
Check erefl : (1, Yes) == (1, Maybe) = false.
*)

Check 'I_3. (* [0..n) *)
Print ordinal.

Definition tri_to_ord (t : tri) : 'I_3 :=
    match t with
    | Yes => inord 0
    | No => inord 1
    | Maybe => inord 2
    end.
Print inord.

Definition ord_tri (o : 'I_3) : tri :=
    match (o : nat) with
    | 0 => Yes
    | 1 => No
    | _ => Maybe
    end.

Lemma ord_triK : cancel tri_to_ord ord_tri.
Proof.
by case ; rewrite /ord_tri /tri_to_ord inordK.
Qed.

Definition tri_eqMixin := CanEqMixin ord_triK.
Canonical tri_eqType := EqType tri tri_eqMixin.

Check (1, Yes) == (1, Maybe).
(* Check erefl : (1, Yes) == (1, Maybe) = false. *)

Record record : predArgType := Mk_record {
    A : nat;
    B : bool;
    C : nat * nat;
}.

Definition record_to_triple (r : record) : (nat * bool * (nat * nat)).
Proof. move: r ; by case. Defined.
Definition triple_to_record (t : (nat * bool * (nat * nat))) : record :=
    match t with
    | (a, b, c) => Mk_record a b c
    end.
Lemma record_tripleK : cancel record_to_triple triple_to_record.
Proof.
by case.
Qed.

Definition record_eqMixin := CanEqMixin record_tripleK.
Canonical record_eqType := EqType record record_eqMixin.

Variable test : record.
Check (test == test).
Compute (Mk_record 1 true (2, 3)) == (Mk_record 2 true (2, 3)).

(* Odd and even numbers *)

Structure odd_nat := Odd {
    oval :> nat;
    oprop : odd oval
}.
Check @Odd 3 erefl.
Compute odd 3.

Lemma oddP (n : odd_nat) : odd n.
Proof.
by case: n.
Qed.

Structure even_nat := Even {
    eval :> nat;
    eprop : ~~ (odd eval)
}.
Definition e2 := Even (erefl (~~ (odd 2))).
Compute e2 + 3.
Lemma evenP (n : even_nat) : ~~ (odd n).
Proof. by case: n. Qed.

(** Part 1: Arithmetics **)

Example test_odd (n : odd_nat) :
    ~~ (odd 6) && odd (n * 3).
Proof. Fail by rewrite oddP evenP. Abort.

Canonical even_0 : even_nat := @Even 0 isT.

Lemma oddS n : ~~ (odd n) -> odd n.+1.
Proof. done. Qed.

Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Proof.
case: n => // n /= ; by rewrite negbK.
Qed.

Canonical odd_even (m : even_nat) : odd_nat :=
    @Odd m.+1 (oddS (eprop m)). 
Canonical even_odd (m : odd_nat) : even_nat :=
    @Even m.+1 (evenS (oprop m)).

Lemma foo (m : even_nat) : odd m.+1.
Proof.
(* будет строить инстанс odd_nat, чтобы прийти к цели *)
(* который построится благодаря канонам *)
(* oddP : forall n : odd_nat, odd (oval n) *)
(*                            odd S m *)
(* oval ?n === S m  => triggers odd_even *)
(* ?n = odd_even ?m *)
by rewrite oddP.
Qed.

Lemma foo' (m : even_nat) : odd m.+3.
Proof.
by rewrite oddP.
Qed.


Lemma odd_mulP (n m : odd_nat) : odd (n * m).
Proof.
case: n => /= n n0 ; case: m => /= m m0.
by rewrite oddM ; apply/andP.
Qed.




Example test_odd (n : odd_nat) :
  ~~ (odd 6) && odd (n * 3).
Proof.
apply/andP ; split => //.
by rewrite odd_mulP.
Qed.



