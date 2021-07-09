From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Injectivity of constructors *)
Definition succ_inj (n m : nat) :
    n.+1 = m.+1 -> n = m
:=
    fun Sn_Sm : n.+1 = m.+1 =>
        match
            Sn_Sm in (_ = Sm)
            return (n = Sm.-1)
        with
        | erefl => erefl n
        end.

Definition or_introl_inj (A B : Prop) (p1 p2 : A) :
    or_introl p1 = or_introl p2 :> (A \/ B) ->
    p1 = p2
 :=
    fun eq =>
        match
            eq in (_ = oil2)
            return (p1 =
                    if oil2 is or_introl p2' then p2' else p2)
        with
        | erefl => erefl p1
        end.
Definition true_eq_false_implies_false :
    true = false -> False
:=
    fun eq : true = false =>
        match eq in (_ = b)
            return (if b then True else False) 
        with
            | erefl => I
        end.
Definition false_eq_true_implies_false :
    false = true -> False
:=
    fun eq : false = true =>
        match eq in (_ = b)
            return (if b then False else True)
        with
            | erefl => I
        end.
(* Large elimination gives us an opportunity
   to eliminate a term (b) and get a type -
   False or True above. *)
(* Not all universes support this feature *)
Fail Definition or_introl_inj (A B : Prop) (p1 : A) (p2 : B) :
    or_introl p1 = or_intror p2 -> False
 :=
    fun eq =>
        match
            eq in (_ = oil2)
            return (if oil2 is or_introl p2' then False else True)
        with (* we prove True here ...*)
        | erefl => I (* here must be term equal by definition to True *)
        end.

(* Convoy pattern *)
Locate "<>".
Definition neq_irrefl A (x : A) :
    x <> x -> False
:=
    fun neq_xx : x = x -> False =>
        neq_xx (erefl x).

Fail Definition neq_sym' A (x y : A) :
    x <> y -> y <> x
:=
    fun neq_xy : x <> y =>
        fun eq_yx : y = x =>
            match eq_yx in (_ = a)
                return False
            with
            | erefl => _
            end. 

Definition neq_sym A (x y : A) :
    x <> y -> y <> x
:=
    fun neq_xy : x <> y =>
        fun eq_yx : y = x =>
            (match
                eq_yx in (_ = a)
                return (a <> y -> False)
            with
            | erefl => fun neq_yy : y <> y => neq_yy erefl
            end) neq_xy.

(* Proofs by induction *)
Definition congr1 (A B : Type) :
    forall (f : A -> B) (x y : A),
    x = y -> f x = f y
:=
    fun f x y eqxy =>
        match
            eqxy in (_ = a)
            return (f x = f a)
        with
        | erefl => erefl (f x)
        end.

Fail Definition addn0 :
    forall n : nat, n + 0 = n
:=
    fun (n : nat) =>
        match n as a return (a + 0 = a) with
        | O => erefl 0
        | S n' => congr1 S (_ : n' + 0 = n')
        end.
(* Problem: we don't have proof of the same lemma
   for predecesoor. Solution = recursion *)
Definition addn0 :
    forall n : nat, n + 0 = n
:=
    fix rec (n : nat) : n + 0 = n :=
        match n return (n + 0 = n) with
        | O => erefl 0
        | S n' => congr1 S (rec n') (* proof for predecessor *)
        end.
(* Symmetric version is much simpler -> 
   just because addition is defined through
   recursion on 1st argument, so 0 + n is 
   equal by definition to n.
   Something related to symbolic computations *)
Definition add0n :
    forall n : nat, 0 + n = n
:=
    fun n : nat => erefl n.

(* Principle of Mathematical Inducion *)
Definition nat_ind :
    forall (P : nat -> Prop),
        P 0 ->
        (forall n : nat, P n -> P n.+1) ->
         forall n : nat, P n
:=
    fun P =>
    fun p0 : P 0 =>
    fun step : (forall n : nat, P n -> P n.+1) =>
        fix rec (n : nat) :=
            match n return (P n) with
            | O => p0
            | S n' => step n' (rec n')
            end.

Definition addn0' :
    forall n : nat, n + 0 = n
:= @nat_ind
    (fun n => n + 0 = n)
    (erefl 0)
    (fun _ IHn => congr1 S IHn).
Print addn0'.
(* with definition below we can have computations... *)
(* Type family indexed by natural numbers *)
Definition nat_rect :
    forall (P : nat -> Type),
        P 0 ->
        (forall n : nat, P n -> P n.+1) ->
         forall n : nat, P n
:=
    fun P =>
    fun p0 : P 0 =>
    fun step : (forall n : nat, P n -> P n.+1) =>
        fix rec (n : nat) :=
            match n return (P n) with
            | O => p0
            | S n' => step n' (rec n')
            end.

Definition addn' : nat -> nat -> nat :=
    @nat_rect
    (fun _ => nat -> nat)
    id
    (fun _ pn => succn \o pn).

Compute addn' 23 34.
(* nat_rect vs nat_ind... *)

(* Type => computationally relevant *)
Print ex.
Print sig.
Print sigT.

Definition Pred n := if n is S n' then nat else unit.

Check erefl : Pred 0 = unit.
Check erefl : Pred 34 = nat.

Definition predn_dep : forall n, Pred n :=
    fun n => if n is S n' then n' else tt.
Check tt.
Check predn_dep 0 : unit.
Check predn_dep 8 : nat.

Check erefl : predn_dep 0 = tt.
Check erefl : predn_dep 3 = 2.

Fail Check erefl : predn_dep 0 = 0.

(* Type inference for dependent types is undecidable *)
Fail Check (fun n => if n is S n' then n' else tt).

(* Yet another definition of pred *)
Definition pred (n : {x : nat | x != 0}) : nat :=
    match n with
    | exist x proof_x_neq_0 => predn x
    end.
(* We ask user to provide a proof that x is not 0 *)
Print exist.
Compute pred (exist (fun x => x != 0) 32 erefl).

Compute pred (exist _ 33 erefl).

Fail Definition pred_fail (n : exists x, x != 0) : nat :=
    match n with
    | ex_intro x proof_x_neq_0 => predn x
    end.