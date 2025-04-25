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
move/andP.
case=> AB BA.
move/subsetP in AB; rewrite /sub_mem in AB.
move/subsetP in BA; rewrite /sub_mem in BA.
apply/eqP; apply/setP.
rewrite /eq_mem=> x.
apply/idP/idP.
apply: AB. apply: BA.
Qed. (* Remarque 1.2.1 *)
Check eqEsubset. 
Check (@set0 T). (* Notation 1.2.3 *)
Check powerset. (* Notation 1.2.4 *)
Print setD. (* Notation 1.2.4 *)
Lemma my_powersetE (A B : {set T}) : (B \subset A) = (B \in powerset A).
Proof. by unfold powerset; rewrite in_set. Qed.
Check powersetE. (* Proposition 1.2.1 *)
Lemma my_card_powerset (E : {set T}) : #|powerset E| = 2 ^ #|E|.
Proof. rewrite cardsE. simpl. 
(* find a way to enumerate E *)
Admitted.
Check card_powerset.
Lemma Ex_1_2_1_4 (E : {set T}) n: #|E| = n -> #|powerset E| = 2 ^ n.
Proof. move=> H0. by rewrite my_card_powerset H0. Qed. (* Exercice 1.2.1.4 *) 
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


End Definition_of_a_set.
