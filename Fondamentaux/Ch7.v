From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(**
In this chapter, some properties and examples related to Relation are 
demonstrated except those concerning a concrete number set.
*)

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

Proposition lexicographique : 
  
End Relation_d'ordre.
