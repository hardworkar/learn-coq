From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Axiom replace_with_your_solution_here : forall {A : Type}, A. *)



(** * Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)
Print ex.
Definition and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B
:= conj
(fun existsAB : exists (_ : A), B =>
  match existsAB with
  | ex_intro x px => conj x px
  end)
(fun ab : A /\ B =>
  match ab with
  | conj a b => ex_intro _ a b
  end).


(** * Exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:=
  fun proof : (a1, b1) = (a2, b2) =>
    match
      proof in (_ = (aa, bb))
      return (a1 = aa) /\ (b1 = bb)
    with
    | erefl => conj (erefl a1) (erefl b1)
    end.

(*
(** * Exercise (optional) *)
Definition J :
  forall (A : Type) (P : forall (x y : A), x = y -> Prop),
    (forall x : A, P x x erefl) ->
    forall x y (p : x = y), P x y p
:= replace_with_your_solution_here.
*)

(** * Exercise *)
Definition false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False
:= fun n : nat =>
    fun n1_0 : n.+1 = 0 =>
      match
        n1_0 in (_ = a)
        return (if a is 0 then False else True)
      with
      | erefl => I
      end.

Print nat_ind.
(** * Exercise *)
Definition addnS_rec :
  forall m n, m + n.+1 = (m + n).+1
:=
  fix rec (m n : nat) : m + n.+1 = (m + n).+1 :=
    match m return (m + n.+1 = (m + n).+1) with
    | O => erefl n.+1
    | S m' => congr1 S (rec m' n)
    end.

Definition addnS_helper :
  forall n m, m + n.+1 = (m + n).+1
:= fun n =>
  @nat_ind
  (fun m => m + n.+1 = (m + n).+1)
  (erefl n.+1)
  (fun _ IHmn => congr1 S IHmn).

(* ... yes? *)
Definition addnS :
  forall m n, m + n.+1 = (m + n).+1
:= fun m n => addnS_helper n m.

(* somehow it was not in scope... *)
Definition eq_sym_clean A (x y : A) :
    x = y -> y = x
:= fun pf =>
    match pf with
    | erefl => erefl
    end.

(** * Exercise *)
Print associative.
Definition addA : associative addn
:=
  fix rec (x y z : nat) : x + (y + z) = x + y + z :=
    match x return x + (y + z) = x + y + z with
    | O => erefl (y + z)
    | S x' => congr1 S (rec x' y z)
    end.
Print commutative.
Print eq_trans.

Variable t : nat.
Check (add0n t).
Check (addn0 t).
(** * Exercise (optional): *)
Definition addnC : commutative addn
:= fix rec (x y : nat) :
    x + y = y + x :=
      match
        y return x + y = y + x
      with
      | O => eq_trans (addn0 x) (eq_sym_clean(add0n x))
      | S y' =>
      (let proof1 := addnS x y' :  x + y'.+1  = (x + y').+1 in
       let proof_ind := rec x y' : x + y' = y' + x in
       let proof2 := congr1 S proof_ind : (x + y').+1 = (y' + x).+1 in
       let proof3 := eq_trans proof1 proof2 : x + y'.+1 = (y' + x).+1 in
       proof3)
      end.
Print left_commutative.
(** * Exercise: *)
(* dunno i saw it through commutativity... *)
Definition addnCA : left_commutative addn
:=
  fun (x y z : nat)  =>
    (let proof1 := congr1 (fun d => d + z) (addnC x y) : x + y + z = y + x + z in 
     let proof2 := addA x y z : x + (y + z) = x + y + z in
     let proof3 := addA y x z : y + (x + z) = y + x + z in
     eq_trans (eq_trans proof2 proof1) (eq_sym_clean proof3) 
     ).


(** * Exercise (optional):
Formalize and prove
 - bool ≡ unit + unit,
 - A + B ≡ {b : bool & if b then A else B},
 - A * B ≡ forall b : bool, if b then A else B,
where ≡ means "is isomorphic to".
 *)


(** * Exercise (optional): *)
Definition unit_neq_bool:
  unit <> bool
:= replace_with_your_solution_here.
