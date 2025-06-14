From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Théorie_des_ensembles.

(**
In this section, we use finType to create sets with finite elements, 
however, we avoid using any properties related to the finity, 
since the definition of sets in this chapter is more general.
*)

(* two results from the last chapter *)

Lemma my_contra : forall A B : Prop, (A -> B) -> (~ B -> ~ A).
Proof.
by move=> A B H0 H1 H2; apply: H1; apply: H0.
Qed.
Hypothesis classic : forall A : Prop, (~ ~ A) = A.
Lemma my_contra_inv : forall A B : Prop, (~ B -> ~ A) -> (A -> B).
Proof.
move=> A B H0.
rewrite -(classic A) -(classic B).
exact: my_contra.
Qed.

(* p30: P(x) is a proposition and P is called a predicate. *)
Variables E F : finType.
(* p43 Prop 2.2.2 no proof *)
Proposition exneg_negforall (P : E -> Prop):
  (exists x : E, ~ P(x)) -> ~ (forall x : E, P(x)).
Proof.
case => x notPx H.
by have Px := H x.
Qed.
Proposition negex_forallneg (P : E -> Prop):
  ~ (exists x : E, P(x)) -> forall x : E, ~ P(x).
Proof.
by move=> H x Px; case: H; exists x.
Qed.
Proposition negforall_exneg (P : E -> Prop): 
  ~ (forall x : E, P(x)) -> (exists x : E, ~ P(x)).
Proof.
apply: my_contra_inv.
rewrite classic=> H0.
move=> x.
rewrite -(classic (P x)).
move : x.
exact: negex_forallneg.
Qed.
