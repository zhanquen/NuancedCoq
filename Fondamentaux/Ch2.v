From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(* two results from the last chapter *)
Check contra. (* ∀ c b : bool, (c → b) → ~~ b → ~~ c*)
Check contraLR. (* ∀ c b : bool, (~~ c → ~~ b) → b → c*)

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

Section Quantificateur.

(**
In this section, we use finType to create sets with finite elements, 
however, we avoid using any properties related to the finity, 
since the definition of sets in this chapter is more general.
*)

(* p30: P(x) is a proposition and P is called a predicate. *)

(* p43 Prop 2.2.2 no proof *)
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

Variables E F : finType.
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

End Quantificateur.

Section Inclusion_de_deux_ensembles.

Proposition inclusion_réflexitivité (E : finType) (A : {set E}) : A \subset A.
Proof.
apply/subsetP; rewrite /sub_mem.
move=> x.
by [].
Qed.

Proposition inclusion_transitivité (E : finType) (A B C : {set E}) :
  (A \subset B) && (B \subset C) -> (A \subset C).
Proof.
move/andP => [].
move/subsetP; rewrite/sub_mem => H1.
move/subsetP; rewrite/sub_mem => H2.
apply/subsetP; rewrite/sub_mem => x.
move=> H3.
apply: H2.
apply: H1.
by [].
Qed.

Proposition double_inclusion_E (E : finType) (A B : {set E}) : 
  (A \subset B) && (B \subset A) = (A == B).
Proof.
apply/idP/idP.
- move/andP. case=> AB BA. 
  move/subsetP in AB; rewrite /sub_mem in AB; move/subsetP in BA; rewrite /sub_mem in BA.
  apply/eqP; apply/setP; rewrite /eq_mem.
  move=> x.
  apply/idP/idP.
  - exact: AB. 
  - exact: BA.
- move/eqP => H.
  rewrite H.
  rewrite inclusion_réflexitivité.
  by [].
Qed.
  
Proposition pourtout_vide_P (P : pred void) : forall x : void, P x.
Proof.
move=> x.
have H : x \in set0 by [].
move: H.
rewrite in_set0.
by [].
Qed.

Proposition existe_vide_P (P : pred void) : ~ (exists x : void, P x).
Proof.
apply: forallneg_negex.
exact: pourtout_vide_P.
Qed.

Proposition partie_vide_ensemble (E : finType) (A : {set E}) :
  set0 \subset A.
Proof.
apply/subsetP; rewrite /sub_mem.
move=> x.
by rewrite in_set0.
Qed.

Proposition powerset_vide_NE (E : finType) (A : {set E}) : 
  ~~ ((powerset A) == set0).
Proof.
rewrite -subset0.
apply/subsetP; rewrite /sub_mem.
move=> H.
have H1 := H A.
rewrite powersetE inclusion_réflexitivité in_set0 in H1.
move/implyP in H1.
move: H1.
by [].
Qed.

End Inclusion_de_deux_ensembles.
