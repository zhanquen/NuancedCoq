From Coq Require Import Init.Prelude Unicode.Utf8 Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
The file is compiled under mech.v and is used for the test of codex.
*)

Module Arrow.

Variable (A : finType). (* the set of alternatives/outcomes *)

Variable setA : {set A}.

Variable (n'' : nat).

Definition n' := n''.+1.

Definition n := n'.+1.

  Fact leq2n: 2 <= n.
    Proof.
    by []. 
    Qed.

Definition I := 'I_n. (* the set of individuals/agents *)

Variable i : I. (* agent i *)

Record relL :=
  RL {
    L : rel A;
    trL : transitive L;
    asL : antisymmetric L;
    totL : total L
  }. 

Definition rl (r : relL) (x y : A) := (x \in setA) /\ (y \in setA) /\ L r x y.

Variable preference : I -> relL.

Notation "L^n" := (n.-tuple relL). (* preference profile *)

Definition SCfun := L^n -> relL. (* Social Choice *)

Variable F : SCfun. 

Definition Unanimous F := forall r : relL, F [tuple r | i < n] = r.

Definition dictatorial F := exists i : I, forall tup_r : L^n, F tup_r = tnth tup_r i.

Definition IIA F := forall a b : A, forall tup_p tup_q : L^n, 
(forall i, (rl (tnth tup_p i) a b) <-> (rl (tnth tup_q i) a b)) -> 
  ((rl (F tup_p) a b) <-> (rl (F tup_q) a b)).
  
Definition dictatorial_alt F := exists i : I, forall tup_r : L^n, forall a b : A, 
(rl (tnth tup_r i) a b) <-> (rl (F tup_r) a b).

  Lemma DictatorshipToAlt : dictatorial F -> dictatorial_alt F.
  Proof.
  move=> [] i0 Hi0; exists i0; move=> tup_r.
  move=> a b.
  rewrite Hi0.
  by [].
  Qed.

Definition Unanimous_alt F := forall tup_r : L^n, forall a b : A, 
  (forall i, rl (tnth tup_r i) a b) -> (rl (F tup_r) a b).

  Lemma UnaniousToAlt : Unanimous F /\ IIA F -> Unanimous_alt F.
  Proof. 
  move=> [] HUnan HIIA tup_r a b H1.
  pose agent_ref := (@ord0 n').
  pose tup_ref := [tuple (tnth tup_r agent_ref) | i < n].
  rewrite (@HIIA _ _ _ tup_ref).
  - rewrite HUnan.
    apply: H1.
  - move=> i'; split=> H'; [rewrite tnth_map|];apply: H1.
  Qed.

Section two_individuals_and_three_alternatives.

Hypothesis eq_n_2 : n = 2.
  
  Fact eq_n'_1 : n' = 1.
  Proof.
    move/eqP: eq_n_2.
    rewrite /n.
    have -> : 2 = 1 + 1 by [].
    rewrite -addn1.
    rewrite eqn_add2r.
    by move/eqP.
  Qed.

  Let p := (@inord n' 0).
  
  Let q := (@inord n' 1).
  
Hypothesis eq_cardA_3 : #|A| = 3.

  Check [tuple of enum A]. (* enumerate A with tuple *)
  Definition A_enum := [tuple of enum A].
  
  Let a : 'I_#|A|.
    rewrite eq_cardA_3.
    by move: (@inord 2 0).
  Defined.
  
  Let b : 'I_#|A|.
    rewrite eq_cardA_3.
    by move: (@inord 2 1).
  Defined.
  
  Let c : 'I_#|A|.
    rewrite eq_cardA_3.
    by move: (@inord 2 2).
  Defined. 

Theorem Arrow's23 : Unanimous_alt F /\ IIA F -> dictatorial F.
Proof.
move=> [] HUnan HIIA.
Admitted.

End two_individuals_and_three_alternatives.

Section generalarrow.

Hypothesis leq_cardA_3 : #|A| <= 3.

Theorem Arrow's : 2 < #|A| -> (Unanimous F /\ IIA F -> dictatorial F).
Admitted.

End generalarrow.

(**
Section InductiveArrow.

(** If there is a SC function for n agents and m+1 alternatives that is 
unanious_alt, IIA, non-dictatorial,
*)

Variable m : nat.
Hypothesis gt2m : 2 < m.
Variable A : finType.
Variable setA' setA : {set A}.
Variable a : A.
Hypothesis ainsetA : a \in setA.
Hypothesis rel_setAsetA' : setA :\ a = setA'.
Fact anotinsetA' : a \notin setA'.
Proof.
apply/negP => ainsetA'.
rewrite -rel_setAsetA' in ainsetA'.
rewrite setD11 in ainsetA'.
by [].
Qed.


(**
we have to specify that A' \ {a} == A
*)
Check (SCfun A).
Hypothesis (cardA : #|A| = m) (cardA' : #|A'| = m.+1).
Lemma Ind_Arrow: 
(exists F' : (SCfun A'), (Unanimous_alt F') /\ (IIA F') /\ ~(dictatorial_alt F')) -> 
(exists F : (SCfun A), (Unanimous_alt F) /\ (IIA F) /\ ~(dictatorial_alt F)).
Proof.
move=> [] F' [] HunanF' [] HIIAF' HnotDF'.
Check I.
Qed.

End InductiveArrow.

*)

End Arrow.
