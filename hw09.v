From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path order.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Axiom replace_with_your_solution_here : forall {A : Type}, A. *)

Section InsertionSort.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.

(** Insert an element [e] into a sorted list [s] *)
Fixpoint insert e s : seq T :=
  if s is x :: s' then
    if leT e x then e :: s
    else x :: (insert e s')
  else [:: e].

(** Sort input list [s] *)
Fixpoint sort s : seq T :=
  if s is x :: s' then insert x (sort s')
  else [::].

Hypothesis leT_total : total leT.
Hypothesis leT_tr : transitive leT.

(* from lection *)
Lemma insert_path z e s :
    leT z e ->
    path leT z s ->
    path leT z (insert e s).
Proof.
elim: s z=> [/= | x1 s IHs] z; first by move=> ->.
move=> z_le_e /=.
case/andP=> z_le_x1 path_x1_s.
case: ifP.
- by rewrite /= z_le_e path_x1_s => ->.
move=> /= e_gt_x1.
rewrite z_le_x1.
have:= leT_total e x1.
rewrite {}e_gt_x1 /= => x1_le_e.
exact: IHs.
Qed.

(* from lection *)
Lemma insert_sorted e s :
    sorted leT s ->
    sorted leT (insert e s).
Proof.
rewrite /sorted.
case: s=> // x s.
move=> /=.
case: ifP; first by move=> /= ->->.
move=> e_gt_x.
apply: insert_path.
have:= leT_total e x.
by rewrite e_gt_x /=.
Qed.

(* from lection *)
Lemma sort_sorted s :
  sorted leT (sort s).
Proof.
elim: s=> //= x s IHs.
by rewrite insert_sorted.
Qed.

Lemma all_expands s e x :
    leT x e ->
    all (leT e) s ->
    all (leT x) s.
Proof.
move=> x_le_e.
elim: s=> // y s IHs /=.
case/andP.
move=> e_le_y all_es.
apply/andP.
split.
exact: (leT_tr x_le_e e_le_y).
by apply: IHs.
Qed.


Lemma where_are_all_lemmas_about_all e y s :
    all (leT e) (y :: s) -> leT e y.
Proof.
elim: s => //=.
by case/andP.
move=> x s IHs.
by case/andP.
Qed.


Lemma insert_with_all s e :
    sorted leT s ->
    all (leT e) s ->
    e :: s = insert e s.
Proof.
elim: s=> // y s IHs sorted_ys all_ys /=.
case: ifP => //.
move=> e_le_y_false.
move: (where_are_all_lemmas_about_all all_ys).
rewrite e_le_y_false //.
Qed.


Lemma filter_doesnt_break_all (p all_p : pred T) s :
    all all_p s -> all all_p (filter p s).
Proof.
elim: s=> // x s IHs /=.
case/andP=> all_px all_ps.
case: ifP=> px_info.
move=> /=.
apply/andP ; split ; first done.
by rewrite IHs.
by rewrite IHs.
Qed.

Lemma take_insert_from_filter (p : pred T) s x :
    p x ->
    sorted leT s ->
    filter p (insert x s) = insert x (filter p s).
Proof.
move=> px.
elim: s=> //=.
move=> _.
case: ifP => //.
rewrite px //.
move=> e s IHs path_e_s.
case: ifP.
case: ifP.
move=> pe x_le_e /=.
case: ifP => //.
case: ifP => //.
case: ifP => //.
rewrite x_le_e //.
rewrite pe //.
rewrite px //.
move=> pe_false x_le_e /=.
case: ifP.
case: ifP.
rewrite pe_false //.
move: (order_path_min leT_tr path_e_s).
move=> all_le_e_s _ _ /=.
Search all transitive.
move: (all_expands x_le_e all_le_e_s).
move=> all_le_x_s.
rewrite insert_with_all //.
rewrite sorted_filter //.
rewrite (path_sorted path_e_s) //.
by rewrite filter_doesnt_break_all.
rewrite px //.
move=> x_le_e_false.
case: ifP=> pe_info /=.
case: ifP.
case: ifP.
rewrite x_le_e_false //.
move=> _ _.
rewrite IHs //.
rewrite (path_sorted path_e_s) //.
rewrite pe_info //.
case: ifP.
rewrite pe_info //.
move=> _.
rewrite IHs //.
rewrite (path_sorted path_e_s) //.
Qed.

Lemma absurd_insert_filter (p : pred T) s x :
    p x = false ->
    filter p (insert x s) = filter p s.
Proof.
elim: s=> //=.
case: ifP=> //.
move=> e s IHs.
case: ifP=> //.
move=> le_x_e px_false.
case: ifP=> //=.
case: ifP.
rewrite px_false //.
move=> _ pe.
case: ifP => //.
rewrite pe //.
move=> pe_false.
case: ifP => //.
rewrite px_false //.
move=> _.
case: ifP => //.
rewrite pe_false //.
move=> le_x_e_false px_false.
case: ifP => // pe.
rewrite -IHs //=.
case: ifP => //.
rewrite pe //.
rewrite -IHs //=.
case: ifP => //.
rewrite pe //.
Qed.

(** * Exercise *)
Lemma filter_sort (p : pred T) s :
  filter p (sort s) = sort (filter p s).
Proof.
elim: s=> //= x s IHs.
case: ifP=> px /=.
rewrite take_insert_from_filter.
rewrite IHs.
move=> //.
done.
exact: sort_sorted.
by rewrite absurd_insert_filter.
Qed.

(** Hint: you will probably need to introduce a number of helper lemmas *)

End InsertionSort.



Section AccPredicate.

(* To help you understand the meaning of the `Acc` predicate, here is how
 it can be used to write recursive functions without explicitly using recursion: *)


(** * Exercise:  understand how `addn_f` works *)
Section AdditionViaFix_F.

(* First, let's redefine the addition on natural numbers
   using the `Fix_F` combinator: *)
About Fix_F.
Print Fix_F.

(* Fix_F =  
     fun (A : Type) (R : A -> A -> Prop) (P : A -> Type) 
         (F : forall x : A, (forall y : A, R y x -> P y) -> P x) => 
 fix Fix_F (x : A) (a : Acc R x) {struct a} : P x := 
   F x (fun (y : A) (h : R y x) => Fix_F y (Acc_inv a h)) 
	  : forall (A : Type) (R : A -> A -> Prop) (P : A -> Type), 
        (forall x : A, (forall y : A, R y x -> P y) -> P x) -> 
        forall x : A, Acc R x -> P x *)

(* notice we do recursion on the `a : Acc R x` argument *)
Print Acc_inv.
(* To define addition, we first need to choose the relation `R`
   which "connects" successive value.
   In the case of addition `R x y` can simply mean `y = x.+1` *)

Definition R m n := n = m.+1.
Print R.

(* This definition has to be transparent, otherwise
   evaluation will get stuck *)
Definition esucc_inj : injective succn. by move=> n m []. Defined.

(* Every natural number is accessible w.r.t. R defined above *)
Fixpoint acc (n : nat) : Acc R n :=
  if n is n'.+1 then
      Acc_intro n'.+1 (fun y (pf : n'.+1 = y.+1) =>
                         eq_ind n' _ (acc n') y (esucc_inj pf))
  else Acc_intro 0 (fun y contra => False_ind _ (O_S y contra)).

Check acc.
(*
By the way, `forall n : nat, Acc R n` means that `R` is a well-founded
relation: https://en.wikipedia.org/wiki/Well-founded_relation.
*)
Print well_founded.
Print acc.
(* Addition via `Fix_F` *)
Definition addn_f : nat -> nat -> nat :=
  fun m =>
    @Fix_F (nat : Type)
           (R : nat -> nat -> Prop)
           ((fun=> nat -> nat) : (nat -> Type))
           (fun (m : nat) (rec : (forall y : nat, R y m -> (fun=> nat -> nat) y)) =>
              match m return (_ = m -> nat -> nat) with
              | m'.+1 => fun (eq : m = m'.+1) => succn \o rec m' eq
              | 0 => fun=> id
              end erefl)
           (m : nat)
           ((acc m) : Acc R m).

(* This would get stuck if esucc *)
Check erefl : addn_f 2 4 = 6.

Lemma addn_equiv_addn_f :
  addn =2 addn_f.
Proof. by elim=> // m IHm n; rewrite addSn IHm. Qed.


End AdditionViaFix_F.



(** Exercise: implement multiplication on natural numbers using `Fix_F`:
    no explicit recursion, Program Fixpoint or things like that! *)
Section MultiplicationViaFix_F.

Definition eaddn_inj n : injective (addn n).
Proof.
elim: n=> // n IHn x y.
rewrite !addSnnS.
rewrite /injective in IHn.
move=> eqxy.
move: (IHn x.+1 y.+1 eqxy).
apply: esucc_inj.
Defined.

Definition muln_f : nat -> nat -> nat :=
  fun m =>
    @Fix_F (nat : Type)
           (R : nat -> nat -> Prop)
           ((fun=> nat -> nat) : (nat -> Type))
           (fun (m : nat) (rec : (forall y : nat, R y m -> (fun=> nat -> nat) y)) =>
              match m return (_ = m -> nat -> nat) with
              | 0 => fun=> (fun x => 0) 
              | m'.+1 => fun (eq : m = m'.+1) => (fun x => x + (rec m' eq) x)
              end erefl)
           (m : nat)
           ((acc m) : Acc R m).



(* this should not fail *)
Compute muln_f 2 33.
Compute muln_f 1 33.
Compute muln_f 0 33.
Compute muln_f 0 0.
Compute muln_f 123 0.
Check erefl : muln_f 21 2 = 42.

Lemma muln_equiv_muln_f :
  muln =2 muln_f.
Proof. by elim=> // y IHy x ; rewrite mulSn IHy. Qed.


End MultiplicationViaFix_F.



End AccPredicate.