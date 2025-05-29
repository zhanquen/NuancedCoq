From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Logique_Propositionnelle.
(**
In this chapter, we define each proposition as a variable of type bool, which
allows us to prove by using the truth table, though they could be replaced by 
the natural deduction.
*)
Proposition __1_1 : forall P, P && (~~ P) = false. 
Proof.
by case.
Qed.
Proposition __1_2 : forall P, ~~ (~~ P) = P.
Proof.
by case.
Qed.
Proposition Lois_de_De_Morgan__1 : forall P Q, ~~ (P && Q) = ((~~ P) || (~~ Q)).
by case; case.
Qed.
Proposition Lois_de_De_Morgan__2 : forall P Q, ~~ (P || Q) = ((~~ P) && (~~ Q)).
by case; case.
Qed.
Proposition dist_et_Àdroit : (* we could add "À droit" on prop 1.4 *)
  forall P Q R, (P && (Q || R)) = ((P && Q) || (P && R)).
Proof.
by case; case; case.
Qed.
Fact __1_4 : forall P Q, (P = Q) -> (~~ P = ~~ Q).
Proof.
by case; case.
Qed.
Proposition dist_ou_Àdroit : (* no chinese version for this proof *)
  forall P Q R, (P || (Q && R)) = ((P || Q) && (P || R)).
Proof.
move=> P Q R.
have H0 := (dist_et_Àdroit (~~ P) (~~ Q) (~~ R)).
have H1 := __1_4 H0.
rewrite [in LHS]Lois_de_De_Morgan__1 in H1.
rewrite [in RHS]Lois_de_De_Morgan__2 in H1.
rewrite __1_2 in H1.
rewrite [in LHS]Lois_de_De_Morgan__2 in H1.
rewrite ![in RHS]Lois_de_De_Morgan__1 in H1.
rewrite !__1_2 in H1.
by [].
Qed.
Proposition __1_5 : forall P Q : bool, (P ==> Q) = (~~ P) || Q.
Proof.
by case; case.
Qed.
Proposition __1_6 : forall P Q : bool, ~~ (P ==> Q) = P && (~~ Q).
Proof.
by case; case.
Qed.
Proposition __1_7 : forall P Q : bool, (P ==> Q) = ((~~ Q) ==> (~~ P)).
Proof.
by case; case.
Qed.
Proposition __1_8 : forall P Q : bool, (P == Q) = (P ==> Q) && (Q ==> P).
Proof.
by case; case.
Qed.
Proposition __1_9: forall P Q R, ((P ==> Q) && (Q ==> R)) ==> (P ==> R).
Proof.
by case; case; case.
Qed.
End Logique_Propositionnelle.
