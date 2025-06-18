From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(**
---------------------------------------------------------------------------------
A formalization project for the book "Fondamentaux de mathématiques"
Properties in this book concern:
  - Basic proof techniques (Chapter 4);
  - Logics (Chapter 1);
  - The set theory (Chapter 2);
  - Function (Chapter 3);

Author: Zhan JING

Please refer to
  https://speit.sjtu.edu.cn/fr/about/news/37594
for more details.

Date: July 2025

Thanks
  Pierre Jouvelot 
for his insights in Rocq proof assistant and Mathematical-Components libraries.
---------------------------------------------------------------------------------
*)

Section Récapitulatif_des_méthodes_déjÀ_vues.

Variables P Q R: Prop.

Proposition dém_conjonction1 : P /\ Q.
split.
Admitted.

Proposition dém_conjonction2 : P /\ Q.
split; last first.
Admitted.

Proposition dém_implication1 : P -> Q.
move=> H.
Admitted.

Hypothesis classic : forall A : Prop, (~ ~ A) = A.

Lemma my_contra : forall A B : Prop, (A -> B) -> (~ B -> ~ A).
Proof.
by move=> A B H0 H1 H2; apply: H1; apply: H0.
Qed.

Lemma my_contra_inv : forall A B : Prop, (~ B -> ~ A) -> (A -> B).
Proof.
move=> A B H0.
rewrite -(classic A) -(classic B).
exact: my_contra.
Qed.

Proposition dém_implication2 : P -> Q.
apply: my_contra_inv.
Admitted.

Proposition dém_équivalence1 : P <-> Q.
split.
Admitted.

Proposition dém_équivalence2 (P1 : Prop) (H : P <-> P1) : P <-> Q.
rewrite H.
Admitted.

Proposition distinction_cas1 : P \/ Q -> R.
move => [].
Admitted.

Proposition distinction_cas2 : P \/ Q -> R.
case.
Admitted.

Variable E : finType.

Variable Pr : pred E.

Proposition dém_prop_univ1 : forall x : E, Pr x.
move=> x.
Admitted.

Proposition dém_prop_univ2 : (exists x0 : E, ~ Pr x0) -> ~ (forall x : E, Pr x).
Proof.
move => [] x0 H H0.
have H1 := H0 x0.
by [].
Qed.

(** 
for the rest of the methods , refer to Ch2.v
*)

Proposition exneg_negforall (T : finType) (P : pred T) :
  (exists x : T, ~~ P(x)) -> ~ (forall x : T, P(x)).
Proof.
case=> x.
move/negP => notPx.
move=> H.
have H1 := H x.
by [].
Qed.

Proposition negex_forallneg (T : finType) (P : pred T) :
  ~ (exists x : T, P(x)) -> forall x : T, ~~ P(x).
Proof.
move=> H x; apply/negP.
move=> H1.
case: H.
by exists x.
Qed.

Proposition negforall_exneg (T : finType) (P : pred T) : 
  ~ (forall x : T, P(x)) -> (exists x : T, ~~ P(x)).
Proof.
apply: my_contra_inv.
rewrite classic=> H0.
move=> x.
rewrite -(classic (P x)).
move/negP=> H.
move: H; apply/negP.
move: x.
exact: negex_forallneg.
Qed.

Proposition forallneg_negex (T : finType) (P : pred T) : 
  (forall x : T, ~~ P(x)) -> ~ (exists x : T, P(x)).
Proof.
apply: my_contra_inv.
rewrite classic.
move => [] x H.
apply: exneg_negforall.
exists x.
exact/negPn.
Qed.
(* ??? unicit/ *)

Search (exists! _, _).
End Récapitulatif_des_méthodes_déjÀ_vues.
