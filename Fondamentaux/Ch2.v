From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Théorie_des_ensembles.
(**
p30: P(x) is a proposition and P is called a predicate.
*)
Check nat.
Variables E F : finType.
(**
Hypothesis EM : forall A : Prop, (~ ~ A) = A.
Lemma contra_inv : forall A B : Prop, (~ B -> ~ A) -> (A -> B).
Proof.
move=> A B H.
have H1 : ~ ~ A -> ~ ~ B by apply: impliesPn.
by rewrite !EM in H1.
Qed.
*)
Proposition exneg_negforall (P : pred E):
  (exists x : E, ~ P(x)) -> ~ (forall x : E, P(x)).
Proof.
case => x notPx H.
by have Px := H x.
Qed.
Proposition negex_forallneg (P : pred E):
  ~ (exists x : E, P(x)) -> forall x : E, ~ P(x).
Proof.
by move=> H x Px; case: H; exists x.
Qed.

(* p44 chinese translation error: no set F *)
Proposition échange_pourtout (P : pred (E * F)) : 
  (forall x : E, forall y : F, P(x,y)) <-> (forall y : F, forall x : E, P(x,y)).
Proof.
by split=> [H y x|H x y]; apply: H.
Qed.

Proposition échange_existe (P : pred (E * F)): 
  (exists x : E, exists y : F, P(x,y)) <-> (exists y : F, exists x : E, P(x,y)).
Proof.
(* p44 Prop 2.2 no proof *)
by split; [move=> [] x [] y Pxy|move=> [] y [] x Pyx]; 
  (* the existence in the presequent could be moved into hypothesis *)
  [exists y; exists x| exists x; exists y].
  (* the existence is applied *)
Qed.
End Théorie_des_ensembles.
