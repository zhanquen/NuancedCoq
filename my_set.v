From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(**
A formal proof for simple conclusions concerning finite set, classical logic and 
functions over finite set.
*)
Section Definition_of_a_set.
Variable T : finType.
Check {set T}. (* Definition 1.2.1 *)
Check nat. (* Notation 1.2.1 *)
Check in_set. (* Notation 1.2.2 *)
Check setP. (* Definition 1.2.3 *)
Check eqEsubset.
Lemma my_eqEsubset (A B : {set T}) : (A \subset B) && (B \subset A) -> (A :==: B).
Proof.
move/andP. case=> AB BA. 
move/subsetP in AB; rewrite /sub_mem in AB; move/subsetP in BA; rewrite /sub_mem in BA.
apply/eqP; apply/setP.
rewrite /eq_mem=> x.
apply/idP/idP. (* ??? *)
apply: AB. apply: BA.
Qed. (* Remarque 1.2.1 *)
Check eqEsubset. 
Check (@set0 T). (* Notation 1.2.3 *)
Check sub0set. (* Example 1.2.5 *) (* Admis *)
Check powerset. (* Notation 1.2.4 *)
Print setD. (* Notation 1.2.4 *)
Lemma my_powersetE (A B : {set T}) : (B \subset A) = (B \in powerset A).
Proof. by unfold powerset; rewrite in_set. Qed.
Check powersetE. (* Proposition 1.2.1 *)
(* ??? cardinality is not well defined *)
Lemma my_card_powerset (E : {set T}) (n : nat) : #|E| = n -> #|powerset E| = 2^n.
Proof.
elim: n=> [H0 | n Hn].
  rewrite expn0.
  move/eqP: H0. rewrite cards_eq0. move/eqP. move=> H0.
  rewrite H0. rewrite /powerset.
  have my_subset0: forall A : {set T}, (A == set0) = (A \subset set0).
    move=> A.
    rewrite eqEsubset.
    rewrite sub0set.
    apply/idP/idP.
      by move/andP; case; move=> H1 H2.
    by move=> H1; apply/andP; rewrite //.
  apply/eqP.
  Check cards_eq0. (* Admis *)
  apply/cards1P.
  exists set0.
  by apply/eqP; rewrite eqEsubset; apply/andP; split; 
    apply/subsetP=> A; rewrite !in_set; rewrite subset0.
  Check card.
move=> H0.
have zeroenumE : 0 < #|E| by rewrite H0; apply: ltn0Sn.
rewrite card_gt0 in zeroenumE.
move: zeroenumE; move/set0Pn.
move=> [] x H1.
move: H0.
rewrite -(setD1K H1).
rewrite cardsU1.
rewrite setD11 //=.
rewrite -{1}(@addn1 n).
rewrite addnC.
move/eqP; rewrite eqn_add2r; move/eqP=> H2.
rewrite expnS.
Admitted.
(* ??? *) (* find a way to enumerate E *)
Check card_powerset.
(* Exercice 1.2.1.4 *) 
Print setI. (* Notation 1.3.1 *)
Lemma my_subsetIl (A B : {set T}) : A :&: B \subset A.
Proof. 
apply/subsetP=> x. rewrite in_setI. move/andP=> [H0 H1]. trivial. 
Qed. 
Lemma my_subsetIlr (A B : {set T}) : (A :&: B \subset A) /\ (A :&: B \subset B).
Proof. by split; apply/subsetP=> x; rewrite in_setI; move/andP=> [H0 H1]. Qed.
(* Remarque 1.3.1 *)
Check subsetIl.
Check subsetIr.
Lemma my_subsetUlr (A B : {set T}) : (A \subset A :|: B) /\ (B \subset A :|: B).
Proof. by split; apply/subsetP=> x; rewrite in_setU => H0; apply/orP; [left|right]. Qed.
(* Remarque 1.3.2 *)
Check setX. (* Notation 1.3.3 *)
Lemma my_setIUl (A B C: {set T}) : (A :|: B) :&: C :==: (A :&: C) :|: (B :&: C).
Proof. 
rewrite eqEsubset; apply/andP; split; apply/subsetP=> x.
  rewrite in_setI; move/andP; case; rewrite in_setU; move/orP. 
  by case=> H0 H1; rewrite in_setU; apply/orP; [left|right]; rewrite in_setI; apply/andP; split.
by rewrite in_setU; move/orP; case; rewrite in_setI; move/andP; case=> H0 H1; 
rewrite in_setI; apply/andP; split; rewrite //; rewrite in_setU; apply/orP; 
[left|right].
Qed. (* Exercice 1.3.1.2 *)
Variables (A B C : {set T}).
Print setD.
Lemma my_setDIr : A :\: (B :|: C) :==: (A :\: B) :&: (A :\: C).
Proof. 
rewrite eqEsubset; apply/andP; split; apply/subsetP=> x.
  rewrite in_setD. move/andP. case. move=> H0 H1. 
  rewrite -in_setC setCU in_setI in H0. move/andP in H0. case: H0=> H00 H01.
  rewrite in_setI. apply/andP. split;
  rewrite in_setD; apply/andP; split; trivial; rewrite -in_setC; trivial.
rewrite in_setI; move/andP; case=> H0 H1. rewrite in_setD. apply/andP.
rewrite in_setD in H0; rewrite in_setD in H1.
move/andP in H0; move/andP in H1.
case: H0 => H00 H01.
case: H1 => H10 H11.
split; trivial.
rewrite -in_setC.
rewrite setCU. (* ??? *)
rewrite in_setI; apply/andP; split; rewrite in_setC; trivial.
Qed. (* Exercice 1.3.1.3 *)
Lemma my_cardsX (A1 A2 : {set T}) (n p : nat) : 
  (#|A1| == n /\ #|A2| == p) -> #|setX A1 A2| == n * p.
move=> [] H0 H1.
Qed. (* Exercice 1.3.1.4 *)
End Definition_of_a_set.

Section my_Logic.
Hypothesis classic : forall P:Prop, ~ ~ P -> P.
Corollary impnotnot: forall P:Prop, P -> ~ ~ P.
Proof. by move=> P H0 []. Qed. (* Proposition 2.2.1.1 *)
Lemma eq_PnotnotP : forall P:Prop, P <-> ~ ~ P.
Proof. split; [apply: impnotnot|apply: classic]. Qed. (* Proposition 2.2.1.1 *)
Corollary contraAB (A B : Prop): (A -> B) -> (~ B -> ~ A).
Proof. move=> H0 H1. rewrite/not => H2. apply: H1. apply: H0. apply: H2. Qed.
Lemma negP_or (A B : Prop) : ~ (A \/ B) <-> ~ A /\ ~ B.
Proof. 
split; move=> H0.
  by split; move: H0; apply: contraAB; move=> H0; [left|right].
by move: H0; case; move=> H0 H1; rewrite/not; case.
Qed. (* Proposition 2.2.1.2 *)
Corollary contraBA (A B : Prop): (~ B -> ~ A) -> (A -> B).
Proof. move=> H0 H1. apply: classic. have notnotA : ~ ~ A by apply: impnotnot.
move: notnotA. exact: contraAB. Qed.
Lemma negP_and (A B : Prop) : ~ (A /\ B) <-> ~ A \/ ~ B.
Proof.
split; move=> H0; last by move: H0; case; apply: contraAB; case; move=> H0 H1.
move: H0. apply: contraBA. move=> H0. apply: impnotnot. 
by split; move: H0; rewrite negP_or; case; move=> H0 H1; apply: classic.
Qed. (* Proposition 2.2.1.3 *)
Lemma notAorB (A B : Prop) : (~ A \/ B) -> (A -> B).
Proof.
move=> [] H0 H1.
  by absurd A.
trivial.
Qed.
Lemma impAB_notAorB (A B : Prop) :(A -> B) -> (~ A \/ B).
Proof.
move=> H0.
rewrite (@eq_PnotnotP B).
rewrite -negP_and.
case; move=> H1 H2.
absurd B.
  trivial.
exact: H0.
Qed. (* Proposition 2.2.2.1 *)

Lemma notimpAB_AandnotB (A B : Prop) : ~ (A -> B) <-> (A /\ ~ B).
Proof.
split; move=> H0; last first.
  case: H0=> H0 H1 H2.
  absurd B.
    trivial.
  exact: H2.
split.
  apply: classic.
  move: H0.
  apply: contraAB.
  move=> H0 H1.
  by [].
move: H0.
apply: contraAB.
move=> H0 H1.
trivial.
Qed. (* Proposition 2.2.2.2 *)
Lemma Ex221324 (A B : Prop) :  (A /\ (A -> B)) -> B.
Proof. case=> H0 H1. exact: H1. Qed. (* Exercice 2.2.1.3.1 *)
Lemma Ex221325 (A B : Prop) : (A -> B) <-> (~ B -> ~ A).
Proof. by split; move=> H0; [apply: contraAB|apply: contraBA]. Qed. (* Exercice 2.2.1.3.2 *)
End my_Logic.
