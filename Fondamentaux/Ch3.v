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

Print fonc_comp_assoc.

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

Proposition image_union :
  f @: (E' :|: E'') = f @: E' :|: f @: E''.
Proof.
apply/setP/subset_eqP/andP; split; apply/subsetP; rewrite/sub_mem => y.
- move/imsetP => [] x.
  rewrite in_setU.
  move/orP => [] H0 H1; rewrite in_set.
  - apply/orP; left.
    by apply/imsetP; exists x.
  - apply/orP; right.
    by apply/imsetP; exists x.
- rewrite in_setU.
  move/orP => [].
  - move/imsetP => [] x H0 H1.
    apply/imsetP.
    exists x; last by [].
    rewrite in_setU.
    by rewrite H0.
  - move/imsetP => [] x H0 H1.
    apply/imsetP.
    exists x; last by [].
    rewrite in_setU.
    rewrite H0.
    exact: orbT.
Qed.

Proposition image_inter :
  f @: (E' :&: E'') \subset f @: E' :&: f @: E''.
Proof.
apply/subsetP; rewrite/sub_mem => y.
move/imsetP => [] x H0 H1.
rewrite in_setI in H0; move/andP in H0.
move: H0 => [] H00 H01.
rewrite in_setI.
by apply/andP; split; apply/imsetP; exists x.
Qed.

Variables F' F'' : {set F}.

Proposition image_réciproque_vide :
  f @^-1: set0 = set0.
Proof.
apply/eqP.
rewrite -subset0.
apply/subsetP; rewrite/sub_mem => x.
rewrite/preimset. (** definition of preimset *)
rewrite in_set in_set0.
by [].
Qed.

Proposition image_réciproque_Image :
  f @^-1: (f @: [set: E]) = [set: E].
Proof.
apply/setP/subset_eqP/andP; split.
- rewrite/preimset.
  apply/subsetP; rewrite/sub_mem => x; rewrite in_set.
  move => H0.
  by rewrite in_setT.
- apply/subsetP; rewrite/sub_mem => x H0.
  rewrite in_set.
  apply/imsetP.
  exists x; first by [].
  by [].
Qed.

Proposition subset_stable_réciproque :
  F' \subset F'' -> f @^-1: F' \subset f @^-1: F''.
Proof.
move => H0.
apply/subsetP; rewrite/sub_mem => x.
rewrite/preimset !in_set => H1.
move/subsetP in H0.
rewrite/sub_mem in H0.
exact: H0.
Qed.

Proposition réciproque_union :
  f @^-1: (F' :|: F'') = f @^-1: F' :|: f @^-1: F''.
Proof.
apply/setP/subset_eqP/andP; split; apply/subsetP; rewrite/sub_mem => x.
- rewrite/preimset.
  move=> H0.
  rewrite in_set in_setU in H0.
  rewrite in_setU.
  rewrite !in_set.
  by [].
- by rewrite/preimset !in_set.
Qed.

Proposition réciproque_inter :
  f @^-1: (F' :&: F'') = f @^-1: F' :&: f @^-1: F''.
Proof.
apply/setP/subset_eqP/andP; split; apply/subsetP; rewrite/sub_mem => x.
- rewrite/preimset.
  rewrite in_set.
  move=> H0.
  rewrite in_setI in H0.
  rewrite in_setI.
  rewrite !in_set.
  by [].
- by rewrite/preimset !in_set.
Qed.

End Définitions_et_premiers_exemples.

Section Injectivité_Surjectivité.

Variables (E F G : finType) (f : E -> F) (g : F -> G).

Proposition comp_inj1 :
  (injective f) /\ (injective g) -> injective (g \o f).
Proof.
case => H0 H1.
move => x x'.
rewrite /= => H2.
apply: H0.
apply: H1.
by [].
Qed.

Proposition comp_inj2 :
  injective (g \o f) -> injective f.
Proof.
move => H0 x x' H1.
have H2 : g (f x) = g (f x') by rewrite H1.
apply: H0.
rewrite /=.
by [].
Qed.

Definition surjective (E' F' : finType) (f' : E' -> F') := 
  forall y : F', exists x : E', y = f' x.

Proposition imfF_surj_E :
  surjective f <-> (f @: E == [set: F]).
Proof.
split.
- move => H0.
  apply/eqP/setP/subset_eqP/andP; split.
  - apply/subsetP; rewrite/sub_mem => y.
    by rewrite in_set.
  - apply/subsetP; rewrite/sub_mem => y.
    move => H1.
    apply/imsetP.
    move: (H0 y) => [x H2].
    by exists x.  
- move/eqP.
  move => H0 y.
  move/setP/subset_eqP/andP in H0.
  move: H0 => [H1 H2].
  move/subsetP in H2.
  rewrite/sub_mem in H2.
  have/imsetP H3 := H2 y (in_setT y).
  move: H3 => [x H4 H5].
  by exists x.
Qed.
  
Proposition comp_surj1 : 
  (surjective f) /\ (surjective g) -> surjective (g \o f).
Proof.
move => [H0 H1] z.
have H2 := (H1 z); move: H2 => [y H2].
have H3 := (H0 y); move: H3 => [x H3].
exists x.
rewrite /= -H3.
by [].
Qed.
(* p118 Prop 3.8 typo: y = f(x) *)

Proposition comp_surj2 :
  surjective (g \o f) -> surjective g.
Proof.
move=> H0 z.
have/= H1 := H0 z.
move: H1 => [x H1].
exists (f x).
by [].
Qed.


End Injectivité_Surjectivité.


Section Bijectivité.

Variables (E F : finType) (f : E -> F).

Definition my_bijective := injective f /\ surjective f.

(**
??? : a problem of cop raises here: we are not allowed to define {ffun ...}
when we encounter the composition.
*)
Proposition carac_bij31 :
  (exists g , (g \o f =1 @id E) /\ (f \o g =1 @id F)) -> my_bijective.
Proof.
move=> [g [Hgf Hfg]].
rewrite/my_bijective; split.
- apply: (@comp_inj2 _ _ _ _ g).
  rewrite/injective=> x x'; rewrite/eqfun in Hgf.
  by rewrite !Hgf.
- Check comp_surj2.
  apply: (@comp_surj2 _ _ _ g f).
  rewrite/surjective.
  rewrite/eqfun in Hfg.
  move=> y; exists y.
  by rewrite !Hfg.
Qed.

Proposition carac_bij12 : 
  my_bijective -> forall y : F, exists! x : E, y = f x.
Proof.
move=> [Hi Hs] y.
move: (Hs y) => [x H0].
exists x.
rewrite/unique; split; rewrite //.
rewrite/injective in Hi.
move => x' Hx'.
move: (Hi x x').
rewrite -Hx' H0 => H1.
exact: H1.
Qed.

(**
??? : How can we create a function with help of the existence predicate?
https://proofassistants.stackexchange.com/questions/4013/bijections-on-coq
*)

Proposition carac_bij23 : (forall y : F, {x : E | f x = y /\ (forall z, f z = y -> x = z) }) 
  -> exists g0 , (g0 \o f =1 @id E) /\ (f \o g0 =1 @id F).
Proof.
move=> g.
exists (fun y => proj1_sig (g y)).
split; rewrite/eqfun.
- move=> x; rewrite/=.
  apply (proj2 (proj2_sig (g (f x))) x).
  by [].
- move=> y; rewrite/=.
  apply (proj2_sig (g y)).
Qed.

Variable g : F -> E.

Lemma cond_surjective : f \o g =1 @id F -> surjective f.
Proof.
rewrite/eqfun/surjective => H y.
have/= Hy := H y.
exists (g y).
by rewrite Hy.
Qed.

Lemma cond_injective : g \o f =1 @id E -> injective f.
Proof.
rewrite/eqfun/=/injective => H x1 x2 H12.
have H12' : g (f x1) = g (f x2) by rewrite H12.
rewrite !H in H12'.
by [].
Qed.

Variable (f' : {ffun E -> F}) (F' : {set F}).

Proposition cohérence_de_inverse  : 
 (g \o f' =1 @id E) /\ (f' \o g =1 @id F) -> f' @^-1: F' == g @: F'.
move => [] H0 H1.
apply/eqP/setP/subset_eqP/andP; split; apply/subsetP; rewrite/sub_mem => x.
- rewrite/preimset in_set => Hl.
  apply/imsetP.
  exists (f' x); first by [].
  rewrite /eqfun/= in H0.
  by rewrite H0.
- move/imsetP => [y Hy Hxy].
  rewrite/preimset in_set.
  rewrite Hxy.
  rewrite/eqfun/= in H1.
  rewrite H1.
  by [].
Qed.
 
End Bijectivité.

Section Prop_bij.

Variable (E F G : finType) (f : {ffun E -> F}) (g : {ffun F -> G}).

Proposition comp_bijective : my_bijective f /\ my_bijective g -> my_bijective (g \o f).
Proof.
move => [Hf Hg].
apply: carac_bij31.
Admitted.

End Prop_bij.

Section Prod_cartesien.

Variable E : finType.

Variable n : nat.
Hypothesis n0 : 0 < n.
Variable E' : 'I_n -> {set E}.

Hypothesis UE : \bigcup_ (i : 'I_n) E' i == [set: E].

Section Def_prod_cartesien.


Variable x : 'I_n -> E.
Hypothesis xi : forall i : 'I_n, x i \in E' i.

Definition phi := [tuple (x i) | i < n].

End Def_prod_cartesien.

Check phi.

Proposition tuple_application : bijective phi.
Proof.
Admitted.
End Prod_cartesien.
Section Complément.

Variable E : finType.

Let PE := powerset [set: E].

Theorem de_Cantor : 
  ~ (exists f : {ffun E -> (set_of_finType E)}, 
    (forall y : (set_of_finType E), exists x : E, f x = y)).
Proof.
move=> [f Hf].
have H1 := Hf [set x0 : E | x0 \notin (f x0)]; move: H1 => [x H1].
have [] := boolP (x \in f x) => H2.
- have H2' := H2; rewrite H1 in_set in H2' ; move/negP in H2'.
  by [].
- have H2' : x \in f x by rewrite H1 in_set.
  by move/negP in H2.
Qed.

Variable F : finType.

Theorem FixedPoint : 
  (exists phi : {ffun E -> {ffun E -> F}}, surjective phi) -> 
    forall f : {ffun F -> F}, exists s : F, (f s) = s.
Proof.
move=> [phi Hphi]; move=> f.
pose q := finfun (fun a => f (phi a a)).
move: (Hphi q)=> [p Hp].
exists (phi p p).
rewrite -{2}Hp.
by rewrite ffunE.
Qed.


Variable (A : {set E}) (f : {ffun E -> E}).
Hypothesis (Imf : f @: E \subset A).

Variable (C : nat -> {set E}).

Hypothesis rec_C : forall n : nat, C n.+1 == f @: (C n).

Lemma Lemme_de_CB : 
  injective f -> exists g, g @: E \subset A /\ bijective g.
Proof.
move => H.
Admitted.

Theorem de_Cantor_Bernstein :
  exists f1 : {ffun E -> F}, exists f2 : {ffun F -> E}, injective f1 /\ injective f2 -> 
    (exists f3 : {ffun E -> F}, bijective f3).
Proof.
Admitted.


Definition my_False : forall Pp : Prop, Pp -> Pp.
move=> Pp.
move=> pp.
by [].
Qed.
Check my_False.
Print my_False.

End Complément.



