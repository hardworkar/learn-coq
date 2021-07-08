From mathcomp Require Import ssreflect ssrfun.
Set Implicit Arguments.

Module MyNamespace.

(* Type theory <=> Higher-order logic *)
(* proof = program, formula it proves = type for the program *)
(* return type = theorem *)
(* arguments = hypotheses *)
(* code/terms = proof *)

(* types = propositions *)
(* terms = proofs *)
Definition A_implies_A (A : Prop) :
    A -> A
:= fun proof_of_A : A => proof_of_A.

Definition A_implies_B_implies_A (A B : Prop) :
    A -> B -> A
:= fun proof_A => fun proof_B => proof_A.
Print A_implies_A.

Definition modus_ponens (A B : Prop) :
    A -> (A -> B) -> B
:= fun pA pAimliesB => pAimliesB pA.

(* Conjunction *)
Inductive and (A B : Prop) : Prop :=
    | conj of A & B.
Notation "A /\ B" := (and A B) : type_scope.

(* AAAAAA!!!! [prod]:
Inductive prod (A B : Prop) : Prop :=
    | pair of A & B.
prod => pair of types (terms)
conj => pair of props (proofs)
*)
Definition andC (A B : Prop) :
    A /\ B -> B /\ A :=
fun pAndB =>
    match pAndB with
    | conj pA pB => conj pB pA
    end.

(* Disjunction *)
Inductive or (A B : Prop) : Prop :=
    | or_introl of A
    | or_intror of B.
Notation "A \/ B" := (or A B) : type_scope.
Arguments or_introl [A] B _, [A B] _.
Arguments or_intror  A [B] _, [A B] _.
(* Again - similiar to sum type *)

Definition and_or_distr (A B C : Prop) :
    (A \/ B) /\ C -> (A /\ C) \/ (B /\ C)
:= fun '(conj paob pc) =>
    match paob with
    | or_introl pa => or_introl (conj pa pc)
    | or_intror pb => or_intror (conj pb pc)
    end.

(* The true proposition *)
Inductive True : Prop :=
    | I.

Definition anything_implies_True (A : Prop) :
    A -> True
:= fun _ => I.

Definition True_and_True :
    True /\ True
:= conj I I.

(* Falsehood *)
Inductive False : Prop := .

Definition exfalso_quodlibet {A : Prop} :
    False -> A
:= fun pF : False => match pF with end. (* no branches *)

Definition a_or_false_implies_a (A : Prop) :
    A \/ False -> A
:= fun paof =>
    match paof with
    | or_introl pa => pa
    | or_intror pf => exfalso_quodlibet pf
    end.

(* Negation - something strange... *)
Definition not (A : Prop) := A -> False.
Notation "~ A" := (not A) : type_scope.

(* A -> ~ ~ A <=> A -> ((A -> False) -> False) *)
Definition double_negation_introduction (A : Prop) :
    A -> ~ ~ A
:= fun pa : A => fun pna : ~ A => pna pa. 

(* Equivalence *)
Definition iff (A B : Prop) := (A -> B) /\ (B -> A).
Notation "A <-> B" := (iff A B) : type_scope.

(* Universal quantifier *)
(* proof of forall x.P(x) transforms any t into a proof P(t)
   => dependently typed function *)
(* forall x : T, P x, where P : T -> Prop is a predicate:
   "\x.[x = 0]" - predicate, P y = "y = 0" - proposition *)
Definition forall_andD (A : Type) (P Q : A -> Prop) :
    (forall x, P x /\ Q x) ->
    (forall x, P x) /\ (forall x, Q x)
:= fun all_pq =>
    conj
        (fun x => match all_pq x with conj px _ => px end)
        (fun x => match all_pq x with conj _ qx => qx end).

(* Existential quantifier: provide pair (x, proof[P x]) *)
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    | ex_intro (x : A) (proof : P x).

Check ex_intro.

Notation "’exists’ x : A , P" :=
  (ex (fun x : A => P))
    (at level 200, right associativity).

Notation "'exists' x .. y , p" :=
    (ex (fun x => .. (ex (fun y => p)) ..))
    (at level 200, x binder, right associativity,
    format "'[' 'exists' '/  ' x .. y , '/  ' p ']'")
    : type_scope.

Definition exists_not_forall A (P : A -> Prop) :
    (exists x, P x) -> ~ (forall x, ~ P x)
:=
    fun x_px : exists x, P x =>
        fun all_npx : forall x, ~ P x =>
            match x_px with
            | ex_intro x px => all_npx x px
            end.
Check exists_not_forall.

Definition curry_dep A (P : A -> Prop) Q :
    ((exists x, P x) -> Q) -> (forall x, P x -> Q)
:=
    fun f : (exists x, P x) -> Q =>
        fun x : A =>
            fun px : P x =>
                f (ex_intro P x px).

(* Propositional equality *)
Inductive eq (A : Type) (x : A) : A -> Prop :=
    | eq_refl : eq x x.
(* We give eq_refl one argument, it returns term with type eq x x *)
(* Notice that second x is an index. First is a parameter *)
Check eq.
Check eq_refl.
Notation "x = y" := (eq x y) : type_scope.
Arguments eq_refl {A x}, {A} x.

Check eq_refl 0 : 0 = 0.
Check eq_refl : 0 = 0.
Check eq_refl : (fun _ => 0) 42 = 0. 
Check eq_refl : 2 + 2 = 4.
Fail Check eq_refl : 0 = 1.

Variables A B : Type.
Variable f : A -> B.

Check eq_refl : f = f.

(* a-renaming *)
Check eq_refl : (fun x => x) = (fun y => y).

(* n-expansion *)
Check eq_refl : (fun x => f x) = f.

Definition eq_reflexive A (x : A) :
    x = x
:= 
    eq_refl x.
(* Dependent pattern matching *)
Definition eq_sym_unannotated A (x y : A) :
    x = y -> y = x
:= fun (pf : x = y) =>
    (match pf with
    | eq_refl => (eq_refl x : x = x)
    end) : y = x.

Definition eq_sym A (x y : A) :
    x = y -> y = x
:= fun (pf : x = y) =>
    match
        pf in (_ = b) (* give new name to y-index : b *)
        return (b = x)
    with
    | eq_refl => eq_refl x
    end.

Definition eq_sym_clean A (x y : A) :
    x = y -> y = x
:= fun pf =>
    match pf with
    | eq_refl => eq_refl
    end.


Definition eq_trans A (x y z : A) :
    x = y -> y = z -> x = z
:= fun pf_xy : x = y =>
    match
        pf_xy in (_ = b)
        return (b = z -> x = z)
    with (* unification x :=: b !!*)
    | eq_refl => fun (pf_xz : x = z) => pf_xz
    end.
  
Definition eq_trans_clean A (x y z : A) :
    x = y -> y = z -> x = z
:= fun pf_xy =>
    match pf_xy with | eq_refl =>
        fun pf_yz =>
            match pf_yz with | eq_refl =>
                eq_refl
            end 
    end.
(* looks exactly like eq_trans btw *)
Definition eq_trans_as_fuck A (x y z : A) :
    x = y -> y = z -> x = z
:= fun pf_xy : x = y =>
    match
        pf_xy in (_ = a)
        return (a = z -> x = z)
        with | eq_refl =>
        (* to this moment we unificate x and y. there is only x now. kind of sad, cause below pf_yz : x = z *)
            fun pf_yz : x = z => pf_yz
    end.