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

Proposition distinction_cas : P \/ Q -> R.
move => [].

End Récapitulatif_des_méthodes_déjÀ_vues.
