From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(**
In this chapter, some properties and examples related to Relation are 
demonstrated except those concerning a concrete number set.
*)

Section Relation_d'équivalence.

Variable E : finType.

Variable (rE : rel E).

Variables (trE : transitive rE) (rrE : reflexive rE) (srE : symmetric rE).

Variable rE_equivalence : transitive rE /\ reflexive rE /\ symmetric rE.

Lemma equiv_E_repres (x y : E) : 
  [set z | rE x z] = [set z | rE z y] <-> rE x y.
Proof.
split.
- move/setP/subset_eqP/andP => []; move/subsetP; rewrite/sub_mem => H0 H1.
  have H := H0 x.
  rewrite !in_set in H.
  move: (H (rrE x)).
  by [].
- move => H0.
  apply/setP/subset_eqP/andP => []; split; apply/subsetP; rewrite/sub_mem => z'.
  - rewrite in_set.
    move => H1.
    rewrite srE in H1.
    rewrite in_set.
    exact: (trE H1 H0).
  - rewrite !in_set srE => H1.
    exact: (trE H0 H1).
Qed.

Variable R : {set E}.

(* Hypothesis H_R1 : forall x y, (x \in R) && (y \in R) -> x != y -> ~ (rE x y). *)

Hypothesis H_R2 : forall z : E, exists! x : E, (x \in R) && (z \in [set z0 | rE x z0]).

Proposition classe_equivalence_partition : 
  [set: E] != set0 -> 
  ([set: E] = \bigcup_ ( x in R ) [set z | rE x z]) /\ 
  (forall x, x \in R -> [set z | rE x z] != set0) /\
  (forall x y, x \in R /\ y \in R /\ x != y -> [disjoint [set z | rE x z] & [set z | rE y z]])
  .
move=> H0.
split; last first.
- split.
  - move=> x' H1.
    apply/set0Pn.
    exists x'.
    rewrite in_set.
    exact: rrE.
  - move=> x' y' [H1 [H2 H6]].
    rewrite -setI_eq0.
    apply: negbNE.
    apply/set0Pn.
    move => [z]; rewrite in_setI !in_set.
    move/andP => [H3].
    rewrite srE => H4.
    have H5 := trE H3 H4.
    apply equiv_E_repres in H5.
    have H7 := H_R2 z.
    rewrite/unique in H7.
    move: H7 => [x'' [H7 H8]].
    have Hx' := H8 x'; rewrite H1 in_set //= in Hx'.
    have Hx'0 := Hx' H3.
    have Hy' := H8 y'; rewrite H2 in_set srE //= in Hy'.
    have Hy'0 := Hy' H4.
    rewrite -Hx'0 -Hy'0 in H6.
    by move/negP: H6 => [].
- apply/setP/subset_eqP/andP; split; apply/subsetP; rewrite/sub_mem => x H1.
  - apply/bigcupP.
    have H2 := H_R2 x.
    move: H2 => [x0].
    rewrite/unique//=.
    move => [/andP [H2 H3] H4].
    exists x0.
      by rewrite H2.
    by [].
    (* p264 mistake: please refer to this line *)  
  - by rewrite in_setT.
Qed.

End Relation_d'équivalence.

Section Relation_d'ordre.

Variables E F : finType.

Variables (rE : rel E) (rF : rel F).

Variables (trF : transitive rF) (rrF : reflexive rF) (arF : antisymmetric rF).

Variables (trE : transitive rE) (rrE : reflexive rE) (arE : antisymmetric rE).

Variables rEor : transitive rE /\ reflexive rE /\ antisymmetric rE.

Variables rFor : transitive rF /\ reflexive rF /\ antisymmetric rF.

Let rEstor := [rel x y | (x != y) && rE x y].

Proposition antisym_Estor : antisymmetric rEstor.
Proof.
move => x y /=.
rewrite andbA.
move/andP => [H0 H1]; move: H0.
move/andP => [H0 H2]; move: H0.
move/andP => [H0 H3].
apply: arE.
by rewrite H1 H3.
Qed.

Proposition tr_Estor : transitive rEstor.
Proof.
move => x y z /=.
move/andP => [H0 Hyz].
move/andP => [H1 Hxz].
apply/andP; split; last first.
- exact: (trE Hyz).
- apply/negP.
  move/eqP => eq_yz.
  rewrite eq_yz in H0.
  rewrite eq_yz in Hyz.
  have eq_xz : x == z.
    apply/eqP.
    apply: antisym_Estor.
    rewrite/rEstor /= andbA.
    by rewrite H1 Hxz H0 Hyz.
  move/negP in H1.
  by [].
Qed.

(**
p270 Remarque 7.1 does not provide a clear reason for antisymetrique;
and antireflexive could be demonstrated with antisymetrique
*)

Let lexic := [rel p p' | (rEstor p.1 p'.1) || ((p.1 == p'.1) && (rF p.2 p'.2))].

Proposition lexicographique_order : 
  reflexive lexic /\ antisymmetric lexic /\ transitive lexic.
Proof.
split; [|split].
- move => p; rewrite/lexic/=.
  apply/orP; right.
  apply/andP; split; first by apply/eqP.
  apply: rrF.
- move => p1 p2; rewrite/lexic/=.
  move/andP => [H1 H2].
  move/orP: H2 => []; move/andP => [H20 H21]; move/orP: H1 => []; move/andP => [H10 H11].
  - have H : (rE p1.1 p2.1) && (rE p2.1 p1.1) by apply/andP; split.
    have/eqP H' := arE H.
    move/negP in H10.
    by [].
  - rewrite eq_sym in H10.
    move/negP in H20.
    by [].
  - rewrite eq_sym in H20.
    move/negP in H10.
    by [].
  - apply/pair_eqP; rewrite /=; apply/andP; split; first by [].
    have H : (rF p1.2 p2.2) && (rF p2.2 p1.2) by apply/andP; split.
    have/eqP H' := arF H.
    by [].
- move => p1 p2 p3; rewrite/lexic/=.
  move => r21 r13.
  move/orP: r21 => []; move/andP => [r210 r211]; move/orP: r13 => []; move/andP => [r130 r131].
  - apply/orP; left.
    - have H : (rEstor p2.1 p3.1).
      by apply: (@tr_Estor p1.1); rewrite/rEstor/=; apply/andP; split.
      by [].
  - apply/orP; left; apply/andP; split.
    - move/eqP: r130 <-.
      by [].
    - apply: (trE r211).
      move/eqP: r130 <-.
      exact: rrE.
  - apply/orP; left; apply/andP; split.
    - move/eqP: r210 ->.
      by [].
    - apply: (trE _ r131).
      move/eqP: r210 ->.
      exact: rrE.
  - apply/orP; right; apply/andP; split.
    - move/eqP: r210 ->.
      move/eqP: r130 ->.
      by [].
    - exact: (trF r211).
Qed.

End Relation_d'ordre.
