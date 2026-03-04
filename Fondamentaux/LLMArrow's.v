From Coq Require Import Init.Prelude Unicode.Utf8 Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

(* Verified in nix-shell:
   - Coq: 8.17.1
   - MathComp (ssreflect): 1.17.0
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  move=> [j Hj]; exists j => tup_r a b.
  by rewrite Hj.
  Qed.

Definition Unanimous_alt F := forall tup_r : L^n, forall a b : A, 
  (forall i, rl (tnth tup_r i) a b) -> (rl (F tup_r) a b).

  Lemma UnaniousToAlt : Unanimous F /\ IIA F -> Unanimous_alt F.
  Proof. 
  move=> [Hun Hii] tup_r a b Hall.
  pose r0 := tnth tup_r ord0.
  pose const_r0 : L^n := [tuple r0 | i < n].
  have Hpair : forall i, (rl (tnth tup_r i) a b) <-> (rl (tnth const_r0 i) a b).
    move=> i.
    rewrite /const_r0 tnth_mktuple.
    split.
    - move=> _; rewrite /r0; exact: Hall ord0.
    - move=> _; exact: Hall i.
  have Hii_ab := Hii a b tup_r const_r0 Hpair.
  have HFconst : rl (F const_r0) a b.
    rewrite /const_r0 Hun /r0.
    exact: Hall ord0.
  by move: Hii_ab => [_ H]; exact: H HFconst.
  Qed.

End Arrow.
