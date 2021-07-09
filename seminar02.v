Section PropositionalLogic.

Variables A B C : Prop.

Definition anb1 :
  A /\ B -> A
:= fun pAandB =>
    match pAandB with
    | conj pA pB => pA
    end.

Definition impl_trans :
  (A -> B) -> (B -> C) -> A -> C
:= fun pAB : A -> B => fun pBC : B -> C => fun a : A =>
    pBC (pAB a).

Definition HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C
:= fun pABC : A -> B -> C =>
    fun pAB : A -> B =>
        fun a : A =>
            pABC a (pAB a).

Definition double_negation_introduction :
    A -> ~ ~ A
:= fun pa : A => fun pna : ~ A => pna pa. 

Definition DNE_triple_neg :
  ~ ~ ~ A -> ~ A
(* (((A -> False) -> False) -> False) -> (A -> False) *)
:= fun f : ~ ~ ~ A =>
    fun pA =>
        f (double_negation_introduction pA).

Definition or_comm :
  A \/ B -> B \/ A
:= fun AorB : A \/ B =>
    match AorB with
    | or_introl pA => or_intror pA
    | or_intror pB => or_introl pB
    end.

End PropositionalLogic.



Section Quantifiers.

Variable T : Type.
Variable A : Prop.
Variable P Q : T -> Prop.
Definition forall_conj_comm :
  (forall x, P x /\ Q x) <-> (forall x, Q x /\ P x)
:= conj
    (fun allx_PQ => fun x => match allx_PQ x with conj px qx => conj qx px end) 
    (fun allx_QP => fun x => match allx_QP x with conj qx px => conj px qx end). 

Definition forall_disj_comm :
  (forall x, P x \/ Q x) <-> (forall x, Q x \/ P x)
:= conj
    (fun allx_PQ =>
    fun x =>
        match allx_PQ x with
        | or_introl px => or_intror px
        | or_intror qx => or_introl qx
        end)
    (fun allx_QP =>
    fun x =>
        match allx_QP x with
        | or_introl qx => or_intror qx
        | or_intror px => or_introl px
        end).
Definition not_exists_forall_not :
  ~(exists x, P x) -> forall x, ~P x
:= fun not_existPx : (exists x, P x) -> False =>
    fun x => fun px : P x =>
        not_existPx (ex_intro P x px).

Definition exists_forall_not_ :
(exists x, A -> P x) -> (forall x, ~P x) -> ~A
:= fun exAPx : exists x, A -> P x =>
    fun allxPx : forall x, ~P x =>
        fun a : A =>
            match exAPx with
            | (ex_intro _ x apx) => (allxPx x) (apx a)
            end.

(*
(** Extra exercise (feel free to skip): the dual Frobenius rule *)
Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2
:=
*)
End Quantifiers.





Section Equality.

(** exercise: *)
Definition f_congr {A B} (f : A -> B) (x y : A) :
  x = y  ->  f x = f y
:= fun xy : x = y =>
    match
      xy in (_ = b)
      return (f x = f b)
    with
    | eq_refl => eq_refl (f x)
    end.

Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
:= fun fg : f = g =>
      match fg in (_ = b)
        return (x = y -> f x = b y) (* "return" specifies type of expression after "with" *)
        with | eq_refl =>
        (* at this stage we unificate f&g. Now we can use only f *)
          fun xy : x = y => 
            match xy in (_ = a)
              return (f x = f a)
              with | eq_refl => eq_refl (f x) end end.
(*
(** extra exercise *)
Definition congId A {x y : A} (p : x = y) :
  f_congr (fun x => x) p = p :=
*)
(* exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= fun a1b1a2b2 : (a1, b1) = (a2, b2) =>
    match a1b1a2b2 in (_ = (aa, bb))
      return (a1 = aa) /\ (b1 = bb)
      with | eq_refl =>
      conj (eq_refl a1) (eq_refl b1) 
      end.

End Equality.



Section ExtensionalEqualityAndComposition.

Variables A B C D : Type.

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
(*
Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation " g \o f " := (compose g f)
  (at level 40, left associativity) : type_scope.
*)
Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:= eq_refl (fun x => h (g (f x))).


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)

(** Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:= fun f => fun x => eq_refl (f x).

(** Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:= fun f => fun g => fun pfg : f =1 g =>
    fun x => match pfg x in (_ = h) return (h = f x) with
    | eq_refl => eq_refl (f x) end.

(** Exercise: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:= fun f => fun g => fun h =>
    fun fg : f =1 g =>
      fun gh : g =1 h =>
        fun x =>
          (* first - we eat fx, only g x exists after this step *)
          match ((eqext_sym f g fg) x) : (g x = f x) in (_ = a) return (a = h x) with | eq_refl =>
          (* now we eat hx, only g x still exists *)
          match                 (gh x) : (g x = h x) in (_ = b) return (g x = b) with | eq_refl =>
              eq_refl (g x)
          end end.

(** Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:= fun f => fun g => fun h => fun fg1_proof =>
  fun x => match fg1_proof x in (_ = gx) return (h \o f) x = (h gx)
  with | eq_refl => eq_refl (h (f x)) end.

(** Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:= fun f => fun g => fun h => fun fg1_proof =>
    fun x => match fg1_proof (h x) in (_ = ghx) return (f \o h) x = ghx
    with | eq_refl => eq_refl (f (h x)) end.

End ExtensionalEqualityAndComposition.


From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:= fun a => fun b => 

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
:=