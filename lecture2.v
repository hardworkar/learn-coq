From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

Definition id :
    forall A : Type, A -> A
:=
    fun A : Type => fun x : A => x.
Compute id bool true.
Compute id nat 34.

(* Dependent types, wow! Type of return value depends on argument *)
Check id bool : bool -> bool.
Check id nat : nat -> nat.

(* A function of type like forall x : A, B is called a dependently
   typed function from A to B(x) where B(x) meand that B may refer
   to x and B is usually called a family of types *)
Locate "->".
(* (forall _ : A, B) - independent, because of _ *)

(* type <=> implementation *)
Definition id' :
    forall A : Type , forall _ : A ,  A
:=
       fun A : Type =>   fun x : A => x.

(* Product Type *)
Inductive prodn : Type := | pairn of nat & nat.

Inductive prod (A B : Type) : Type :=
    | pair of A & B.
(* prod is a type constructor, not a type! *)
Fail Check prod : Type.
Check prod nat nat : Type.

(* 4 arguments!.. - all type parametres of prod are inherited by pair *)
Check pair.
Check pair nat bool 34 true.

(* Implicit arguments *)
Arguments id [A] _.
Arguments pair [A B] _ _.

Check id 34.
Compute id 33.
Fail Check pair nat bool 33 true : prod nat bool.
Check @pair nat bool 33 true : prod nat bool.
Set Implicit Arguments.
Check pair 42 true : prod nat bool.

(* Notations *)
Notation "A * B" :=
    (prod A B)
    (at level 40, left associativity)
    : type_scope.

Locate "*".
Fail Check nat * bool.
Check (nat * bool)%type.
Check (nat * bool) : Type.

Open Scope type_scope.
Locate "*".
Check nat * bool.
Fail Check 34 * 34.
Close Scope type_scope.

(* Left assoc example *)
Check ((nat * bool) * nat)%type.
Check (nat * bool * nat)%type.
Check (nat * (bool * nat))%type.

Notation "( p ; q )" := (pair p q).
Check (1; false).

Notation "( p , q , .. , r )" :=
    (pair .. (pair p q) .. r) : core_scope.
Check (1, false) : nat * bool.
Check (1, false, 3) : nat * bool * nat.
Check (1, false, 3, true) : nat * bool * nat * bool.

Definition fst {A B : Type} : A * B -> A :=
    fun p =>
        match p with
        | (a, _) => a
        end.
Check fst.

Definition snd {A B : Type} : A * B -> B :=
    fun p =>
        match p with
        | (_, b) => b
        end.
Notation "p .1" := (fst p).
Notation "p .2" := (snd p).
Compute (43, true).1.
Compute (43, true).2.

Definition swap {A B : Type} : A * B -> B * A :=
    fun p =>
        match p with
        | (a,b) => (b, a)
        end.
Compute swap (34, true).

(* Sum Type *)
Inductive sum (A B : Type) : Type :=
    | inl of A
    | inr of B.
Notation "A + B" :=
    (sum A B) (at level 50, left associativity)
    : type_scope.
Definition swap_sum {A B : Type} :
    A + B -> B + A :=
    fun s =>
        match s with
        | inl a => inr B a
        | inr b => inl A b
        end.

