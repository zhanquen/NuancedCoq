From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Module Arrow.
Variable (n'' : nat).

Section Voting.

Variables (A : finType). (* the set of outcomes *)
Variable setA : {set A}.
Definition n' := n''.+1.
Definition n := n'.+1.

Fact gt1n: 1 < n.
Proof.
by []. 
Qed.

Definition I := 'I_n. (* the set of agents *)
Variables i : I. (* agent i *)
Record relL :=
  RL {
    L : rel A;
    trL : transitive L;
    asL : antisymmetric L;
    totL : total L
  }. 
Definition rl (r : relL) (x y : A) := (x \in setA) /\ (y \in setA) /\ L r x y.

Variables preference : I -> relL.
(** Define social welfare and social choice *)
Notation "L^n" := (n.-tuple relL). (* preference profile *)
Definition SCfun := L^n -> relL. (* Social Choice *)
Variable F : SCfun. 
Definition Unanimous F := forall r : relL, F [tuple r | i < n] = r.
Definition Unanimous_alt F := forall tup_r : L^n, forall a b : A, 
  (forall i, rl (tnth tup_r i) a b) -> (rl (F tup_r) a b).
Definition dictatorial F := exists i : I, forall tup_r : L^n, F tup_r = tnth tup_r i.
Definition dictatorial_alt F := exists i : I, forall tup_r : L^n, forall a b : A, 
(rl (tnth tup_r i) a b) <-> (rl (F tup_r) a b).

Lemma DictatorshipToAlt : dictatorial F -> dictatorial_alt F.
Proof.
move=> [] i0 Hi0; exists i0; move=> tup_r.
move=> a b.
rewrite Hi0.
by [].
Qed.

Definition IIA F := forall a b : A, forall tup_p tup_q : L^n, 
(forall i, (rl (tnth tup_p i) a b) <-> (rl (tnth tup_q i) a b)) -> 
  ((rl (F tup_p) a b) <-> (rl (F tup_q) a b)).

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

End Voting.

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

End Arrow.





Theorem Arrow's23 : n = 2 /\ #|A| = 3 -> Unanimous F /\ IIA F -> dictatorial F.
Proof.
move=> [] Hn  HA  [] HUnan HIIA.
Admitted.

Theorem Arrow's : 2 < #|A| -> (Unanimous F /\ IIA F -> dictatorial F).
Admitted.
End ArrowThm.
