From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section ArrowThm.
Variables (A : finType).
Variables (n'' : nat).
Definition n' := n''.+1.
Definition n := n'.+1.
Definition I := 'I_n.
Variables i : I.
Record relL :=
  RL {
    L : rel A;
    trL : transitive L;
    asL : antisymmetric L;
    totL : total L
  }. 
Variables preference : I -> relL.
(** Define social welfare and social choice *)
Variable F : n.-tuple relL -> relL. (* SC *)
Notation "L^n" := (n.-tuple relL).
Definition Unanimous F := forall r : relL, F [tuple r | i < n] = r.
Definition Pareto_Efficient F := forall tup_r : L^n, forall a b : A, 
  (forall i, L (tnth tup_r i) a b) -> (L (F tup_r) a b).
Definition dictatorial F := exists i : I, forall tup_r : L^n, F tup_r = tnth tup_r i.
Definition IIA F := forall a b : A, forall tup_p tup_q : L^n, 
(forall i, (L (tnth tup_p i) a b) <-> (L (tnth tup_q i) a b)) -> 
  ((L (F tup_p) a b) <-> (L (F tup_q) a b)).

Lemma UnaniousToAlt : Unanimous F /\ IIA F -> Pareto_Efficient F.
Proof. 
move=> [] HUnan HIIA tup_r a b H1.
pose agent_ref := (@ord0 n').
pose tup_ref := [tuple (tnth tup_r agent_ref) | i < n].
rewrite (@HIIA _ _ _ tup_ref).
- rewrite HUnan.
  apply: H1.
- move=> i'; split=> H'; [rewrite tnth_map|];apply: H1.
Qed.

Theorem Arrow's : 2 < #|A| -> (Unanimous F /\ IIA F -> dictatorial F).
Admitted.
End ArrowThm.
