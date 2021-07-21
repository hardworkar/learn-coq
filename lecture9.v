From Coq Require Import Program.
From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path order.
Global Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Sorting algorithms *)

(* Insertion sort *)
Module Insertion.
Section InsertionSort.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.
Implicit Types s t u : seq T.

(* insert an element e into a sorted list s *)
Fixpoint insert e s : seq T :=
    if s is x :: s' then
        if leT e x then
            e :: s
        else
            x :: (insert e s')
    else [:: e].

(* sort input list s *)
Fixpoint sort s : seq T :=
    if s is x :: s' then
        insert x (sort s')
    else
        [::].

Fail Fixpoint sorted' s : bool :=
    if s is x1 :: x2 :: s' then
        leT x1 x2 && (sorted' (x2 :: s'))
    else true.
Fixpoint sorted' s : bool :=
    if s is x1 :: ((x2 :: s') as tail) then
        leT x1 x2 && (sorted' tail)
    else true.

Print sorted.
Print path.

Lemma sorted_cons x s :
    sorted leT (x :: s) -> sorted leT s.
Proof.
move=> //= ; case: s=> //= e s; move/andP; by case.
Qed.

Definition fake_sort s : seq T := [::].

Lemma sorted_fake_sort s : sorted leT (fake_sort s).
Proof. done. Qed.

Print perm_eq.
Print permP.

(* sorted (sort s) /\ perm_eq s (sort s) *)
Lemma sort_sorted s :
    sorted leT (sort s).
Proof.
elim: s=> [// | x s IHs /=].
Abort.

Lemma insert_sorted e s :
    sorted leT s ->
    sorted leT (insert e s).
Proof.
elim: s=> [// | x1 s IHs].
move=> /=.
move=> path_x1_s.
case: ifP=> [e_le_x1 | e_gt_x1].
- by rewrite /= e_le_x1 path_x1_s.
Abort.

Print total.
Hypothesis leT_total : total leT.

Lemma insert_sorted e s :
    sorted leT s ->
    sorted leT (insert e s).
Proof.
elim: s=> [// | x1 s IHs].
move=> /= path_x1_s.
case: ifP=> [e_le_x1 | e_gt_x1].
- by rewrite /= e_le_x1 path_x1_s.
have:= leT_total e x1.
rewrite {}e_gt_x1.
move=> /= x1_le_e.
move: path_x1_s=> {}/path_sorted/IHs.
case: s=> [|x2 s]; first by rewrite /= x1_le_e.
move=> /=.
case: ifP.
move=> /= -> /= path_x2_s.
by apply/andP.
Abort. (* again... *)

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


Lemma sort_sorted s :
    sorted leT (sort s).
Proof.
elim: s=> [// | x s IHs /=].
by apply: insert_sorted.
Qed.

End InsertionSort.

Arguments sort {T} _ _.
Arguments insert {T} _ _ _.

Section SortIsPermutation.
Variable T : eqType.
Variable leT : rel T.

Lemma count_insert p e s :
    count p (insert leT e s) = p e + count p s.
Proof.
by elim: s=> //= x s; case: ifP=> _ //= -> ; rewrite addnCA.
Qed.

Print perm_eql.
Lemma perm_sort s : perm_eql (sort leT s) s.
Proof.
Search _ (perm_eq ?s1 =1 perm_eq ?s2).
apply/permPl/permP.
elim: s=> //= x s IHs p.
by rewrite count_insert IHs.
Qed.

Lemma mem_sort s : sort leT s =i s.
Proof. by apply: perm_mem; rewrite perm_sort. Qed.

Lemma sort_uniq s : uniq (sort leT s) = uniq s.
Proof. by apply: perm_uniq; rewrite perm_sort. Qed.

End SortIsPermutation.

Section SortProperties.

Variable T : eqType.
Variable leT : rel T.

Lemma sorted_sort s :
    sorted leT s -> sort leT s = s.
Proof.
elim: s=> //= x1 s IHs S.
move: (S) => {}/sorted_cons/IHs /= ->.
move: S=> /=.
case: s=> //= x2 s.
by case/andP=> ->.
Qed.

End SortProperties.
End Insertion.


(* Merge sort *)
Module Merge.

Section MergeSortDef.

Context {disp : unit} {T : orderType disp}.
Implicit Types s t : seq T.

Fixpoint split s : seq T * seq T :=
    match s with
    | [::] => (s, s)
    | [:: x] => (s, [::])
    | [:: x, y & s] =>
        let '(t1, t2) := split s in
        (x :: t1, y :: t2)
    end.
Arguments split : simpl nomatch.
Lemma split_lt1 s2 s1 s :
    1 < size s ->
    split s = (s1, s2) ->
    (size s1 < size s).
Proof.
Admitted.
Lemma split_lt2 s1 s2 s :
    1 < size s ->
    split s = (s1, s2) ->
    (size s2 < size s).
Proof.
Admitted.

Fail Fixpoint merge s t : seq T :=
    match s, t with
    | [::], _ => t
    | _, [::] => s
    | x :: s', y :: t' =>
        if (x <= y)%O then x :: merge s' t else y :: merge s t'
    end.

(*|
Nested `fix`-combinator idiom
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
|*)

Fixpoint merge s t : seq T :=
    let fix merge_s t :=
        match s, t with
        | [::], _ => t
        | _, [::] => s
        | x :: s', y :: t' =>
            if (x <= y)%O
            then x :: merge s' t
            else y :: merge_s  t'
        end
    in merge_s t.

Fail Fixpoint sort s : seq T :=
    match s with
    | [::] => s
    | [:: _] => s
    | _ => let '(s1, s2) := split s in merge (sort s1) (sort s2)
  end.

Print Typing Flags.
Unset Guard Checking.
Print Typing Flags.

Fixpoint sort_unguarded s : seq T :=
    match s with
    | [::] => s
    | [:: _] => s
    | _ => let '(s1, s2) := split s in
            merge (sort_unguarded s1) (sort_unguarded s2)
  end.
Print Assumptions sort_unguarded.
Set Guard Checking.

Program Fixpoint sort s {measure (size s)} : seq T :=
    match s with
    | [::] => s
    | [:: _] => s
    | _ => let '(s1, s2) := split s in
            merge (sort s1) (sort s2)
    end.
Next Obligation.
apply/ltP; rewrite (@split_lt1 s2) //.
by case: s sort H0 H Heq_anonymous=> // x1 [] // _ _ /(_ x1).
Qed.
Next Obligation.
apply/ltP; rewrite (@split_lt2 s1) //.
by case: s sort H0 H Heq_anonymous=> // x1 [] // _ _ /(_ x1).
Qed.
Next Obligation. done. Qed.

End MergeSortDef.

(* Example: using orderType instances *)
Section MergeSortTest.

Compute merge [:: 1; 3; 5] [:: 2; 4; 6].
Compute sort_unguarded [:: 6; 4; 2; 1; 1; 5].
Compute sort [:: 6; 4; 2; 1; 1; 5].

End MergeSortTest.

Section MergeSortCorrect.

Context {disp : unit} {T : orderType disp}.
Implicit Types s t : seq T.

(*| (Optional) exercise |*)
Lemma sort_sorted s :
  sorted (<=%O) (sort s).
Proof.
Admitted.

End MergeSortCorrect.
End Merge.