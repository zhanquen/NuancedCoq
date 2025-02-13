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

Lemma contrap: forall P Q:Prop, (P -> Q) -> ~ Q -> ~ P.
Proof.
move=> P Q pq notq.
intro.
by move: (pq H) => Hq.
Qed.

Lemma impfalse: forall P Q R:Prop, (P -> Q) -> (P -> ~ Q) -> P -> R.
Proof.
move=> P Q R pq pnotq p.
move: (pq p)=> q.
move: (pnotq p).
by case; apply q.
(* by [].*)
Qed.

End Negation.

Section BadInference.

(**
True, False, programme
1. What is True, what is False?

2. a hypothesis
*)
Lemma whatisfalse : forall P: Prop, False -> P.
Proof.
move=> P.
Print False.
case.
Qed.
(** 
the object of type False is comparable to 
an empty set

True is the proposition/condition that the universe
of objects in our discussion satisfy
*)
Lemma whatistrue : forall P: Prop, P -> True.
Proof.
move=> P proof.
Print True.
by [].
Qed.
Definition dyslexic_imp := forall P Q:Prop, (P->Q)->Q->P.

Lemma Bad_dyslexic_imp : dyslexic_imp -> False.
Proof.
rewrite /dyslexic_imp.
move=> imppq_q_p.
Print True.
Print False.
move: (imppq_q_p False True)=> impft_t_f. 
(* forall-elim *)
by apply impft_t_f.
Qed.

Print True.
Lemma emptyTrue : forall P : Prop, P->True.
Proof.
move=> P p.
by [].
Qed.

Lemma imp_negTF : ~True -> False.
Proof.
Print not.
by case.
Qed.

Lemma eq_negTF : ~True <-> False.
Proof.
rewrite /iff.
by apply conj; first by apply imp_negTF.
Qed.

Lemma eq_TnegF : True <-> ~False.
Proof.
rewrite /iff.
apply conj.
  move=> t.
  by rewrite /not.
rewrite /not=> ff.
by [].
Qed.

Definition dyslexic_contrap :=forall P Q:Prop,(P->Q) -> ~P -> ~Q.
Lemma Bad_dyslexic_contrap_imp: dyslexic_contrap -> False.
Proof.
rewrite /dyslexic_contrap.
move=> dc.
move: (dc False True).
rewrite eq_negTF -eq_TnegF.
move=> dc1.
apply dc1.
rewrite //=.
by [].
Qed.

End BadInference.

Section equalityDisjunction.
(**
\/ is left-associated.
*)
Theorem abcd_c : forall (A:Set)(a b c d:A), a=c \/ b= c \/ c=c \/ d=c.
Proof.
move=> A a b c d.
by right;
right;
left.
Qed.

(** Proof it with Ssreflect! *)
Theorem abcd_c1 : forall (A:Set)(a b c d:A), a=c \/ b= c \/ c=c \/ d=c.
Proof.
move=> A a b c d.
by apply or_intror; apply or_intror; apply or_introl.
Qed.
End equalityDisjunction.

Section Intuitionism.
Lemma and_assoc : forall A B C:Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
move=> A B C.
(* case splits on the condition, or saying, objects
in the hypothesis
e.g case on forall n: nat
e.g. case on A/\B in the condition
*)
case=>a.
case=> b c. 
(* by []. *) (* can be solved trivially *)
apply conj.
apply conj.
rewrite //=.
rewrite //=.
by [].
Qed.


Lemma and_imp_dist : forall A B C D:Prop,
   (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
Proof.
move=> A B C D [] imp_ab imp_cd [] a c.
by apply conj; [apply: imp_ab |apply: imp_cd].
Qed.


Lemma not_contrad : forall A : Prop, ~(A /\ ~A).
Proof.
move=> A.
rewrite /not.
case.
move=> a nota.
apply: (nota a).
Qed.

Lemma or_and_not : forall A B : Prop, (A\/B)/\~A -> B.
Proof.
move=> A B [] [a nota|b nota]; by [case: nota|].
Qed.

End Intuitionism.

(* revise the theorems in Intuinism *)

Section FiveCharaClassic.
Definition peirce := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~(~P) -> P.
Definition excluded_middle := forall P:Prop, P\/~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q)->(~P\/Q).

Lemma imp31 : excluded_middle -> peirce.
Proof.
rewrite /excluded_middle /peirce.
move=> H P Q H0.
case: (H P).
by [].
move=> notp.
apply: H0.
move=> p.
by [].
Qed.

Lemma imp12 : peirce -> classic.
Proof.
rewrite /peirce /classic.
move=> H P H0.
apply: (H P False).
move=> H1.
by [].
Qed.
(**
In hypothesis we have
~(~P)
((A->B) -> C) -> A by peirce
we induce that
((~A) -> C) -> A so that
((~P) -> C) -> P
we induce that 
((~P) -> C) because
if (~P) then (~P) , ~(~P) then False then C
we induce that 
P
*)

Lemma imp23 : classic -> excluded_middle.
Admitted.

Lemma imp35 : excluded_middle -> implies_to_or.
Proof.
rewrite /excluded_middle /implies_to_or.
move=> H P Q H0.
case: (H P); last first.
move=> H1; by left.
move=> H1.
right.
apply (H0 H1).
Qed.

Lemma imp32 : excluded_middle -> classic.
Proof.
rewrite /excluded_middle /classic.
move=> proof1.
move=> P.
move=> notnotp.
move: (proof1 P); case.
  by [].
rewrite /not in notnotp.
rewrite /not.
move=> notp.
by move: (notnotp notp).
Qed.



End FiveCharaClassic.


