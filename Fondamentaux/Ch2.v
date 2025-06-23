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

Proposition my_subsetIl (T : finType )(A B : {set T}) : 
  A :&: B \subset A.
Proof. 
apply/subsetP=> x.
rewrite in_setI.
move/andP=> [H0 H1].
trivial.
Qed.

Proposition my_subsetUl (T : finType) (A B : {set T}) : 
  (A \subset A :|: B).
Proof.
apply/subsetP=> x.
rewrite in_setU => H0.
apply/orP.
by left.
Qed.

Proposition my_Ivide (T : finType) (A : {set T}) : 
  A :&: set0 == set0.
Proof.
rewrite -subset0.
rewrite/setI.
apply/subsetP; rewrite /sub_mem=> x.
rewrite in_set.
rewrite in_set0.
case/andP => H0 H1.
by [].
Qed.

Proposition my_Uvide (T : finType) (A : {set T}) : 
  A :|: set0 == A.
Proof.
apply/eqP/setP/subset_eqP.
apply/andP; split; last first.
- by apply my_subsetUl.
- rewrite/setU.
  apply/subsetP; rewrite /sub_mem=> x.
  rewrite in_set.
  rewrite in_set0.
  by move/orP; case.
Qed.


Proposition my_setIlU (T : finType) (A B C: {set T}) :
  A :&: (B :|: C) == (A :&: B) :|: (A :&: C).
Proof.
apply/eqP/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x.
- rewrite/setI/setU !in_set.
  by rewrite Bool.andb_orb_distrib_r.
- rewrite/setI/setU !in_set.
  by rewrite Bool.andb_orb_distrib_r.
Qed.

  
Proposition my_setIUl (T : finType) (A B C: {set T}) : 
  (A :|: B) :&: C == (A :&: C) :|: (B :&: C).
Proof. 
rewrite eqEsubset; apply/andP; split; apply/subsetP=> x.
  rewrite in_setI; move/andP; case; rewrite in_setU; move/orP. 
  by case=> H0 H1; rewrite in_setU; apply/orP; [left|right]; rewrite in_setI; apply/andP; split.
by rewrite in_setU; move/orP; case; rewrite in_setI; move/andP; case=> H0 H1; 
rewrite in_setI; apply/andP; split; rewrite //; rewrite in_setU; apply/orP; 
[left|right].
Qed.

Proposition my_setCU (E : finType) :
  ~: [set: E] == set0.
Proof.
apply/eqP/setP/subset_eqP/andP.
rewrite sub0set; split; last by [].
rewrite/setC.
apply/subsetP; rewrite /sub_mem=> x.
rewrite in_set => H.
have H1 := (@in_setT E x).
rewrite -(@setDv E [set: E]).
apply/setDP.
by split.
Qed.

Proposition my_setCvide (E : finType) :
  ~: set0 == [set: E].
Proof.
rewrite/setC.
apply/eqP/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x;
rewrite in_set.
- rewrite in_setT in_set0.
  by [].
- rewrite in_setT in_set0.
  by [].
Qed.

Proposition AICA_videE (E : finType) (A : {set E}):
  A :&: ~: A == set0.
Proof.
apply/eqP/setP/subset_eqP/andP; split; last by apply sub0set.
rewrite/setI/setC.
apply/subsetP; rewrite /sub_mem=> x.
rewrite !in_set.
move/andP.
move/setDP.
rewrite setDv.
by rewrite in_set0.
Qed.

Proposition AUCA_U (E : finType) (A : {set E}):
  A :|: ~: A == [set: E].
Proof.
apply/eqP/setP/subset_eqP/andP; split; rewrite/setU/setC;
apply/subsetP; rewrite /sub_mem => x; rewrite !in_set; first by [].
rewrite orbN.
by [].
Qed.

Proposition CCA_A (E : finType) (A : {set E}):
  ~: ~: A = A.
Proof.
apply/eqP.
rewrite/setC.
apply/eqP/setP/subset_eqP/andP; split; 
apply/subsetP; rewrite /sub_mem=> x; rewrite !in_set.
- rewrite Bool.negb_involutive.
  by [].
- by rewrite Bool.negb_involutive.
Qed.

Proposition Csubset (E : finType) (A B : {set E}):
  A \subset B <-> ~: B \subset ~: A.
Proof.
split; move/subsetP; rewrite /sub_mem => H; apply/subsetP; rewrite /sub_mem => x.
- rewrite !in_setC.
  apply: contra.
  exact: H.
- apply: contraLR.
  rewrite -!in_setC.
  exact: H.
Qed.

Proposition ABD (E : finType) (A B : {set E}):
  A :\: B == A :&: ~: B.
Proof.
apply/eqP/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x.
- move/setDP; case => H0 H1.
  rewrite/setI in_set in_setC.
  by apply/andP; split.
- rewrite/setI in_set in_setC.
  move/andP; case => H0 H1.
  apply/setDP.
  by split.
Qed.
  
Proposition De_Morgan_CI (E : finType) (A B : {set E}):
  ~: (A :&: B) = ~: A :|: ~: B.
Proof.
apply/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x.
- rewrite/setI/setU/setC.
  rewrite !in_set.
  by rewrite negb_and.
- rewrite/setI/setU/setC.
  rewrite !in_set.
  by rewrite negb_and.
Qed.

Proposition De_Morgan_CU (E : finType) (A B : {set E}):
  ~: (A :|: B) == ~: A :&: ~: B.
Proof.
have H := (@De_Morgan_CI _ (~: A) (~: B)).
rewrite !CCA_A in H.
rewrite -H.
rewrite CCA_A.
by [].
Qed.
End Inclusion_de_deux_ensembles.

Section Produit_Cartesien.

Proposition XAB_vide (E F : finType) (A : {set E}) (B : {set F}) :
  (setX A B == set0) <-> (A == set0) || (B == set0).
Proof.
split; last first.
- have [/eqP|/eqP] := boolP (A == set0)=> A0; rewrite //=; move=> H.
  - rewrite/setX.
    rewrite A0.
    apply/eqP/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x;
      rewrite !in_set//=.
  - move/eqP in H; rewrite H.
    rewrite/setX.
    apply/eqP/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x;
      rewrite !in_set//=.
    by move/andP; case=> H1.
- apply: my_contra_inv.
  move/negP.
  rewrite negb_or.
  move/andP; case.
  move/set0Pn; case => a H0.
  move/set0Pn; case => b H1.
  rewrite -subset0.
  apply/negP.
  apply/subsetP; rewrite /sub_mem.
  move=> H.
  have Hab := H (a, b).
  rewrite in_set0 in_setX in Hab.
  move/implyP in Hab.
  rewrite H0 H1 /= in Hab.
  by [].
Qed.
(* p72 Prop 2.12.1 demonstration a little simple *)

Proposition IXDl (E F : finType) (A B : {set E}) (C : {set F}) :
  setX (A :&: B) C == (setX A C) :&: (setX B C).
Proof.
apply/eqP/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x;
      rewrite !in_set//=.
- rewrite /in_mem /=.
  move/andP => []; move/andP => [] => Ha Hb Hc.
  rewrite /in_mem /=. (* !!! *)
  rewrite andbA. (* !!! *)
  apply/andP; split; rewrite //.
  apply/andP; split; rewrite //.
  apply/andP; split; rewrite //.
- rewrite /in_mem /=.
  rewrite andbA.
  move/andP => []; move/andP => []; move/andP => [] H1 H2 H3 H4.
  apply/andP; split; rewrite //.
  apply/andP; split; rewrite //.
Qed.

End Produit_Cartesien.

Section Famille_de_Partition.

Variable E I : finType.

Variable (A : I -> {set E}) (B : {set E}).

Proposition Ibigcup_Dr :
  B :&: \bigcup_ ( i in I ) A i = \bigcup_ ( i in I ) (B :&: A i).
Proof.
apply/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x;
      rewrite !in_set//=.
- move/andP; case => H0.
  move/bigcupP => [] i0 Hi0 H1.
  apply/bigcupP.
  exists i0; first by [].
  by rewrite/setI in_set H1 H0.
- move/bigcupP => [] i0 Hi0.
  rewrite/setI in_set.
  move/andP => [] H0 H1.
  rewrite H0 /=.
  apply/bigcupP.
  by exists i0; first by [].
Qed.

Proposition Ibigcup_Dl :
  (\bigcup_ ( i in I ) A i) :&: B = \bigcup_ ( i in I ) (A i :&: B).
Proof.
(* p77 Prop 2.13 demonstration not clear *)
rewrite setIC.
rewrite Ibigcup_Dr.
apply/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x.
- move/bigcupP => [] i0 Hi0.
  rewrite/setI in_set.
  move/andP => [] H1 H2.
  apply/bigcupP.
  exists i0; first by [].
  rewrite in_set.
  by rewrite H1 H2.
- move/bigcupP => [] i0 Hi0.
  rewrite/setI in_set.
  move/andP => [] H1 H2.
  apply/bigcupP.
  exists i0; first by [].
  rewrite in_set.
  by rewrite H1 H2.
Qed.

Proposition bigcap_De_Morgan : 
  ~: (\bigcap_ ( i in I ) A i) = \bigcup_ ( i in I ) ~: A i.
Proof.
apply/setP/subset_eqP/andP; split; apply/subsetP; rewrite /sub_mem=> x;
rewrite/setC in_set; last first.
- move/bigcupP.
  move=> [] i0 Hi0.
  rewrite in_set.
  move/negP => H0.
  apply/bigcapP.
  move => H1.
  have H2 := (H1 i0 Hi0).
  by [].
- move/bigcapP => H.
  apply/bigcupP.
  have H1 : exists i : I, ~ (i  \in I → x  \in A i).
  (** Here we deduce again the Proposition negforall_exneg, but in a more
  general way to help us complete the proof
  *)
    move: H.
    apply: my_contra_inv.
    rewrite classic=> H i.
    rewrite -(classic (i  \in I → x  \in A i)).
    move=> H1.
    case: H.
    by exists i.
  case: H1 => i0 H1.
  move/implyP in H1.
  rewrite negb_imply in H1.
  move/andP in H1.
  case: H1 => H1 H2.
  exists i0; first by [].
  rewrite in_set.
  by [].
Qed.
(* p77 Prop 2.13.2.left a typo in the demonstration *)

End Famille_de_Partition.
