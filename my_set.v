From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Definition_of_a_set.
Variable T : finType.
Check {set T}. (* Definition 1.2.1 *)
Check nat. (* Notation 1.2.1 *)
Check in_set. (* Notation 1.2.2 *)
Check setP. (* Definition 1.2.3 *)
Check eqEsubset. (* Remarque 1.2.1 *)
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
Proof. unfold setI. rewrite -{2}(imset_id A). Admitted. (* Remarque 1.3.1 *)
Check subsetIl.
Print proper.
End Definition_of_a_set.
