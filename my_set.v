From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.perm. 
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
Lemma my_powersetE (A B : {set T}) : (B \subset A) = (B \in powerset A).
Proof. by unfold powerset; rewrite in_set. Qed.
Check powersetE. (* Proposition 1.2.1 *)
End Definition_of_a_set.
