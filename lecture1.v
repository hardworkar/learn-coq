From mathcomp Require Import ssreflect.
Module My.
Inductive bool : Type :=
| true
| false.
Check (bool -> bool) : Type.
Check (3, 3 <= 6) : nat*Prop.
Check (fun x:nat => x = 3).
Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).
Check (fun x:bool => (x,x)).
Check fun b => b.
Check (let f := (fun b => b*3) in f).
Check fun (f : bool -> bool) => f true.
Compute (fun b => b) true.

Definition idb := fun b : bool => b.
Check idb.
Check (fun (f : bool -> bool) => f true) idb.
Compute idb false.

Definition negb := 
    fun (b : bool) =>
        match b with
        | true => false
        | false => true
        end.
Check negb.
Compute negb false.

(*
    reductions => Eval with restrictions
*)
Eval cbv delta in negb true.
Eval cbv delta beta in negb true.
Eval cbv delta beta iota in negb true.

(*
    Symbolic computations
*)
Variable c : bool.
Compute idb c.

Compute negb c.


Definition andb (b c : bool) : bool :=
    match b with
    | false => false
    | true => c
    end.

Definition andb' (b c : bool) : bool :=
    match c with
    | false => false
    | true => b
    end.

(*
    they are different, but *extensionally* the same
*)
Compute c.
Compute andb c true.
Compute andb' c true.
Compute andb c false.
Compute andb' c false.

Definition sum :=
    fun a => fun b => fun c => fun d => fun e => a+b+c+d+e.
Definition sum_nice (a b c d e : nat) := a+b+c+d+e.

Compute (sum 1) 2 3 4 5.

Inductive nat : Type :=
| O
| S of nat.
Print nat.
Check O.
Check S O.
Check S (S O).

Definition succn := S.
Compute succn (S O).

(* The best implementation... *)
Definition predn (n : nat) : nat := 
    match n with
    | S x => x
    | O => O
    end.
Compute predn (S O).
Compute predn O.

(* {struct n} - induction on n *)
Fixpoint addn (n m : nat) {struct n} : nat :=
    match n with
    | O => m
    | S n' => S (addn n' m)
    end.
Compute addn (S (S O)) (S (S O)).

Fixpoint addn_idiomatic (n m : nat) : nat :=
    if n is S n' then S (addn_idiomatic n' m) else m.
Compute addn_idiomatic (S (S O)) (S (S O)).

Print addn_idiomatic.
(* fix - for recursive calls ; Fixpoint goes exactly like that *)
Definition addn_no_sugar :=
    fix addn (n m : nat) {struct n} : nat :=
        match n with
        | O => m
        | S n' => S (addn n' m)
        end.

Fixpoint addn' (n m : nat) {struct m} :=
    if m is S m' then S (addn' n m') else n.

(* Again, differencies *)
Variable z : nat.
Compute addn O z.
Compute addn' O z.


(* Mutual recursion *)
Fixpoint is_even (n : nat) : bool :=
    if n is S n' then is_odd n' else true
with is_odd n :=
    if n is S n' then is_even n' else false.
Compute is_even (S O).
End My.

Check My.nat.
Check My.addn.

From mathcomp Require Import ssrbool ssrnat.

Print addb.
About nat.
About S.
Check 45.
Check S (S (S O)).

Set Printing All.
Compute 5 + 4.

Compute Init.Nat.pred 4.

(* Lists! *)
Require Import List.
Check 1::2::3::4::nil.
Compute map (fun x => x*x) (1::2::3::nil).
Compute let l := (1::2::3::4::nil) in l ++ map (fun x => 5 - x) l.

SearchPattern (nat -> nat -> bool).
Search Nat.eqb.
Locate "_ \/ _".

Definition good_fact (n : nat) : (list nat) :=
    let fix dummy k :=
        match k with
        | 0 => 0 :: nil
        | S p => S p :: dummy p
        end
    in
    map (fun x => n-x) (dummy n).
Compute good_fact 10.
Locate ".+1".
Variable x : nat.
Check x.+1.
