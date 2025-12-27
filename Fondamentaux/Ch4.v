From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


(**
1. About "par l'absurde"
We point out that the availability of "Demonstration by contraposition" depends
on "Excluded middle", or equivalently, on "Classic", check Ch0.v.
*)

(**
2. About "Analyse-synthèse"
We search for solutions, so that the predicate P is verified.
This is equivalent to the statement that:
We search for a set E s.t. ∀ x \in E, P(x) and ∀ x \notin E, ~ P(x).

Step Analyse:
Fix x \in E, 
If we have P(x) => Q(x), then Q(x).
We have Q(x) <=> x \in F, and we check x \in F => P(x).

Step analyse:
We note here that if Q(x) <=> x \in F then we only need to verify 
x \in F => P(x) in the step Synthesis.
Because x \notin F => ~ Q(x) => ~ P(x).
As a result, (x \in F) /\ P(x) <=> x \in E.
*)

(**
Not complete, next time read from p158
*
)
