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

End Définitions_et_premiers_exemples.
