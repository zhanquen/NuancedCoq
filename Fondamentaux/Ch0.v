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
  - Some propositions of Relation (Chapter 7);

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

Variables (T : Type) (Pr : T -> Prop).

Proposition dém_univ1 : forall x, Pr x.
move=> x.
Admitted.

Proposition dém_univ2 : (exists x0, ~ (Pr x0)) -> ~ (forall x, Pr x).
Proof.
move => [x0 Hx0] H1.
have H1x0:= H1 x0.
by [].
Qed.

(* *)
(* *)

Proposition dém_absurde : (~ P -> False) -> P.
Proof.
rewrite-/(@not (~P)) classic.
by [].
Qed.

Variable Prn : nat -> Prop.

Proposition dém_récc : forall n : nat, Prn n.
elim=> [].
Admitted.

Variable (E : finType) (P1 P2 : pred E).

Proposition analyse_synthese : exists x : E, P1 x.
have analyse: forall x : E, P1 x -> P2 x by admit.
have set_Pr' := finset P2.
have synthesis : set_Pr' :&: (finset P1) != set0 by admit.
move/set0Pn in synthesis.
move: synthesis => [x]; rewrite in_setI in_set.
move/andP => [H1 H2].
exists x.
by [].
Admitted.

End Récapitulatif_des_méthodes_déjÀ_vues.
