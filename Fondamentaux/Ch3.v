From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Définitions_et_premiers_exemples.

Variables (E F G: finType) (H : Type).

Variables (f : {ffun E → F}) (g : {ffun F → G}) (h : {ffun G → H}).

Proposition fonc_comp_assoc : 
  h \o (g \o f) =1 (h \o g) \o f.
Proof.
rewrite/eqfun => x.
rewrite /=. (* trivial by calculation *)
by [].
Qed.

Proposition Neutralité_de_l'identité_gauche : 
  (@ id F) \o f =1 f.
Proof.
rewrite/eqfun => x.
rewrite /=.
by [].
Qed.

Proposition Neutralité_de_l'identité_droite : 
   f \o (@ id E) =1 f.
Proof.
rewrite/eqfun => x.
rewrite /=.
by [].
Qed.

(* p100 typo : h \o (g \o h) *)

Proposition image_d'une_composée :
  (g \o f) @: E \subset g @: F.
Proof.
apply/subsetP; rewrite/sub_mem => z.
move/imsetP. (** definition of imset *)
move => [] x H0.
rewrite /= => H1.
apply/imsetP.
exists (f x); last by [].
by [].
Qed.

Proposition image_vide : 
  f @: set0 = set0.
Proof.
apply/eqP.
rewrite -subset0.
apply/subsetP; rewrite/sub_mem => y.
move/imsetP.
move=> [] x.
rewrite in_set.
by [].
Qed.

Variables (E' E'' : {set E}).
Hypothesis (E'E : E' \subset E) (E''E : E'' \subset E).
Proposition image_partie :
  E' \subset E'' -> f @: E' \subset f @: E''.
Proof.
move=> H0.
apply/subsetP; rewrite/sub_mem => y.
move/imsetP => [] x H1 H2.
apply/imsetP.
move/subsetP in H0.
rewrite/sub_mem in H0.
exists x; last by [].
apply: H0.
by [].
Qed.


  

End Définitions_et_premiers_exemples.
