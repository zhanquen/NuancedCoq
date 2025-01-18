From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.perm. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
(**
exercises of Coq's Art/Everyday logic with Ssreflect approach
<https://www.labri.fr/perso/casteran/CoqArt/everyday/index.html>
*)


Section Polymorphic.
Lemma id_P : forall P:Prop, P -> P.
Proof.
by move=> P P1.
Qed.

Lemma id_PP : forall P:Prop, (P -> P) -> P -> P.
Proof.
move=> P Hpp.
by apply Hpp.
Qed.
Lemma id_PP2 : forall P:Prop, (P -> P) -> P -> P.
Proof.
move=> P.
by apply id_P.
Qed.
Lemma id_PP3 : forall P:Prop, (P -> P) -> P -> P.
Proof.
move=> P Hpp.
by apply id_P.
Qed.
(* Q: why id_P does not require a type Prop as input ? *)

Lemma imp_trans : forall P Q R :Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
move=> P Q R Hpq Hqr Hp.
by apply Hqr; apply Hpq; apply Hp.
Qed.

Lemma imp_trans2 : forall P Q R :Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
move=> P Q R Hpq Hqr Hp.
by apply (Hqr (Hpq Hp)).
Qed.
(* what is apply here ? any other solutions so we can combine hypotheses? *)
Lemma imp_perm :  forall P Q R :Prop, (P -> Q -> R) -> Q -> P -> R.
Proof.
move=> P Q R Hpqr Hq Hp.
by apply Hpqr; [apply Hp | apply Hq].
Qed.

Lemma imp_perm2 :  forall P Q R :Prop, (P -> Q -> R) -> Q -> P -> R.
Proof.
move=> P Q R Hpqr Hq Hp.
by apply (Hpqr Hp Hq).
Qed.

Lemma ignore_Q : forall P Q R :Prop, (P -> R) -> P -> Q -> R.
Proof.
by move=> P Q R Hpr Hp _; apply (Hpr Hp).
Qed.

Lemma delta_imp :  forall P Q :Prop,(P -> P -> Q) -> P -> Q.
Proof.
move=> P Q Hppq Hp.
by apply (Hppq Hp Hp).
Qed.

Lemma diamond : forall P Q R T:Prop, (P -> Q) -> 
                                  (P -> R) -> 
                                  (Q -> R -> T) -> 
                                  P -> T.
Proof.
move=> P Q R T Hpq Hpr Hqrt Hp.
by apply (Hqrt (Hpq Hp) (Hpr Hp)).
Qed.

Lemma weak_peirce : forall P Q:Prop, ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
(**
by sequence we have hypothesis | we need to prove
((((P → Q) → P) → P) → Q)      | Q
  ((P → Q) → P)                | ((P → Q) → P) → P)
P                              | P -> Q
*)
move=> P Q.
move=> H1.
apply H1.
move=> H2.
apply H2.
move=> Hp.
apply H1. move=> _.
apply H2. move=> _.
by apply H1; move=> _.
Qed.

End Polymorphic.

Section PredicateCalculus.
Variables (A : Set ) (P Q : A->Prop) (R : A->A->Prop).
Theorem ex_symm: (forall a b:A, R a b) -> forall a b:A, R b a.
move=> allRab a b.
by apply (allRab b a).
Qed.
Theorem ex_predicateimply: (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
move=> allpq allP a.
by apply (allpq a (allP a)).
Qed.
Theorem ex_id: (forall a b:A, R a b) -> forall a:A, R a a.
Proof.
move=> allRab a.
by apply (allRab a a).
Qed.
End PredicateCalculus.

Section Negation.

Lemma notF: ~ False.
Proof.
(**
False|-False
``~elim
|-~False
*)
intro.
by [].
Qed.

Lemma notF1: ~ False.
Proof.
(* ? *)
case.
Qed.

Lemma notF2: ~ False.
Proof.
(* ? *)
elim.
Qed.

Lemma doubleneg_neg: forall P:Prop, ~ ~ ~ P -> ~ P. (* |- ~ ~ ~ P -> P -> False *)
Proof.
move=> P.
move=> nnn. 
intro. (* ~ ~ ~ P , P |- False *)
elim nnn. (* ~ ~ ~ P , P |- ~ ~ ~ P; ~ ~ ~ P , P |- ~ ~ P *)
intro.
elim H0.
by [].
Qed.

Lemma casenegimp: forall A B: Prop, ~ A -> B.
(**
for a proof of type
~ A -> B
which is equivalent to
A -> False -> B
we implement case split on the statement above and by a proof of type A, 
we reach the goal by False-elimination
*)
Proof.
move=> A B; case.
Admitted.

Lemma impnotnot: forall P:Prop, P -> ~ ~ P.
Proof.
(** 
write the proof!
*)
move=> P H0.
intro.
elim H.
(* elimination of negation only works on the hypothesis with a type that contains
negation operator *)
by apply H0.
Qed.

End Negation.


