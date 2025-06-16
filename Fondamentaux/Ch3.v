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
by []. (* trivial by calculation *)
Qed.

End Définitions_et_premiers_exemples.
