From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.perm. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
(**
Nuanced assortments.
-- A note to Coq, Ssreflect and MathComp

Zhan JING
*)
Section ProveAThm.
(* What's the link between the proof tree and a Coq-Thm script ? *)

  (** 
An /inference/ is a procedure 
from axiomic hypotheses (with atomic types, we can regard the atomicity as 
well known premisses) 
to a statement (with combinatorical types);
A /statement/ is a result of inference.

Note that simplicity of hypotheses is not proportional to the number of connectors.
e.g. A/\B can be the hypotheses for the conclusion of A.
*)

(**
A proof is an simplification/implicitation of statements with substatements;
An inference is a combination of goals with subgoals.
A proof begins from a statement to axioms;
an inference begins from axioms to a statement.
The two have inversed conventions.
*)

(** 
Constructional rules on inference/proof include /introduction/ and /elimination/.
An introduction introduces/adds a connector in the conclusion domain 
along the inference convention;
An elimination applies/simplifies a connector in the conclusion domain 
along the inference convention.
*)

(**
So, in Coq we try intro-rules when connectors appear in the conclusion domain 
and that interpreting them is easier;
we try elim-rules when bringing connectors into proof is easier.
*)

Variables (A: Prop).
Theorem identite : A -> A.
Proof. (* terms above the bar are hypotheses, they are eliminated in the proof tree *)
intro. (* =>-intro *)
(*alternative 1*)
apply: H. (* axiom leaf *)
(*alternative 2*)
(* by [] *) (* axiom leaf *)
Qed. (* termination of proof *)

Check identite. (* a terminated proof becomes an applicable term *)


End ProveAThm.

Section PredicateLogic.
Theorem abc: forall P: nat -> Prop, (forall x: nat, (P x)) -> (P 0).
Admitted.
Print sig.
(**
/Consistency between predicate terms and propositions/
The introduction of type for a variable together with predicate is the same as 
taking it into account in the hypothesis of the proof/inference procedure.
Along with inference convention:
  1. by introducing forall, we move a domain type from
hypothese to conclusion.
  2. by introducing exists var, the procedure is similar by dependent on var
*)

End PredicateLogic.

Section HilbertSaxiom.
Variables A B C : Prop.
Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C. Proof.
move=> hAiBiC hAiB hA. (* Q1 *)
move: hAiBiC.
apply. (* Q2, Q3 *)
  by [].
by apply: hAiB.
Qed.

Hypotheses (hAiBiC : A -> B -> C) (hAiB : A -> B) (hA : A).
Lemma HilbertS2 : C.
Proof.
apply: hAiBiC; first by apply: hA. (* Q4 *)
exact: hAiB. (* Q5 *)
Qed.

Lemma HilbertS3 : C.
Proof.
by apply: hAiBiC; last exact: hAiB. Qed.

Lemma HilbertS4 : C.
Proof. exact: (hAiBiC _ (hAiB _)). (* Q6 *)
Qed.

Lemma HilbertS5 : C.
Proof.
exact: hAiBiC (hAiB _). (* Q7 *)
Qed. 

Lemma HilbertS6 : C.
Proof. 
exact: HilbertS5. Qed.

Print HilbertS5.
Print HilbertS2.
Print HilbertS.
Check HilbertS.

End HilbertSaxiom.

Print HilbertS5.

Print HilbertS2.
Print HilbertS.

Check HilbertS.

Print bool.
(* Inductive bool : Set := true : bool | false : bool *)

Section Symmetric_Conjunction_Disjunction.
Lemma andb_sym : forall A B : bool, A && B -> B && A. Proof.
case.
  by case.
by [].
Qed.


Lemma andb_sym2 : forall A B : bool, A && B -> B && A. Proof.
by move=> []; case. Qed.

Lemma andb_sym3 : forall A B : bool, A && B -> B && A. Proof. by do 2! case. Qed.

(**
Variables (C D : Prop) (hC : C) (hD : D).

Check (and C D).

Print and.

Print conj. (* Q8 *)
*)

Lemma and_sym : forall A B : Prop, A /\ B -> B /\ A. Proof. by move=> A1 B []. Qed.


(* Inductive and (A : Prop) (B : Prop) : Prop := conj : A -> B -> A /\ B *)

Print or.
Check or.



(* Inductive or (A B : Prop)
 : Prop :=

    or_introl : A → A ∨ B
 | or_intror : B → A ∨ B
. *)

Print or_introl.

Lemma or_sym : forall A B : Prop, A \/ B -> B \/ A.
Proof. by move=> A B [hA | hB]; [apply: or_intror | apply: or_introl]. Qed.

Lemma or_sym2 : forall A B : bool, A \/ B -> B \/ A.
Proof. by move=> [] [] AorB; apply/orP; move/orP : AorB. Qed.

(** What does bool type in Proposition-reflection mean ?*)
Section R_sym_trans.
Variables (D : Type) (R : D -> D -> Prop).
Hypothesis R_sym : forall x y, R x y -> R y x.
Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.
Lemma refl_if : forall x : D, (exists y, R x y) -> R x x. Proof.
move=> x [y Rxy].
exact: R_trans Rxy (R_sym Rxy). (* Q10 *)
Qed.
End R_sym_trans.


(*existence, pourtout*)

Section Smullyan_drinker.
(* paradox by Excluded Middle *)
(** what is False? 
False, also known as Termination is a Proposition that:
  can be introduced by (A/\~A);
  can introduce ~A if A in the hypothesis implies Termination. 

False signifies the existence of negation of one of the hypotheses,
or the existence of a proposition that conflicts with (one of the) prior hypothesis
s.t. we can not introduce it into prior hypothesis.

note that by Print False.
Inductive False : Prop := .
None can introduce False!
False is not an inductive type.
*)

Variables (D : Type)(P : D -> Prop).
Variables (A: Prop).
Print False.
Hypothesis (d : D) (EM : forall A, A \/ ~A).
Lemma drinker : exists x, P x -> forall y, P y.
(**
write proof your self:

(exists y, ~P y)|- exists x, P x -> forall y, P y.
~(exists y, ~P y)|- exists x, P x -> forall y, P y.
\/elim
|- ((exists y, ~P y)\/~(exists y, ~P y)) -> exists x, P x -> forall y, P y.
axiom
|- (exists y, ~P y)\/~(exists y, ~P y). 
|- ((exists y, ~P y)\/~(exists y, ~P y)) -> exists x, P x -> forall y, P y.
=>elim
|- exists x, P x -> forall y, P y.
*)
(**
NB: two different propositions:
exists x, P x -> forall y, P y.
(exists x, P x) -> forall y, P y.

Print ex.
*)
Proof.
case: (EM (exists y, ~P y)) (*case split on EM condition*)
=> [[y notPy]| nonotPy]; (* [case split on exists| have hypothesis nonotPy ]*)
first by exists y. (* existence requires at least a variable in the hypothesis as input *)
(* elim-~ *)

 exists d => _ y; case: (EM (P y)) => //= notPy.

Print not.
Check not.
by case: nonotPy; (* case split on (not P), which is P -> False,  if P is given, no subgoal because of False *)
exists y.
Qed.

Lemma drinker2 : exists x, P x -> forall y, P y. (* exercise*)
Proof.
case: (EM (forall y, P y))=>[allPy|notallPy].
  by exists d=> Pd.
  
(**Try write the proof youself, then prove it
hint: case not(A) equivalents A->False
*)
Admitted.


End Smullyan_drinker.

Section Equality.
(*
rewrite tactic
**)
Variable f : nat -> nat.

Hypothesis f00 : f 0 = 0.
Lemma fkk : forall k, k = 0 -> f k = k.
Proof.
move=> k k0.
by rewrite k0.
Qed.

Lemma fkk2 : forall k, k = 0 -> f k = k. Proof. by move=> k ->. Qed.
Lemma fkk21 : forall k, k = 0 -> f k = k. 
Proof. 
move=> k hyp.
rewrite {} hyp.
by [].
Qed.

Variable f10 : f 1 = f 0.

Lemma ff10 : f (f 1) = 0.
Proof.
by rewrite f10 f00. Qed.

Variables (D : eqType) (x y : D).
(* move/eqP *)
Lemma eq_prop_bool : x = y -> x == y.
Proof. by move/eqP. Qed.
Lemma eq_bool_prop : x == y -> x = y.
Proof. by move/eqP. Qed.
(* problem with negation *)
End Equality.

Section Using_Definition.
Variable U : Type. (* Universe *)
Definition set := U -> Prop. 
(* Proposition on Universe *)
(* Proposition predicating on Universe *)
Definition subset (A B : set) := forall x, A x -> B x.
Definition transitive (T : Type) (R : T -> T -> Prop) := forall x y z, R x y -> R y z -> R x z.
Lemma subset_trans : transitive subset.
Proof.
rewrite /transitive /subset => x y z.
move=> subxy subyz t xt.
by apply: (subyz t); apply: (subxy t).
Qed.

Lemma subset_trans2 : transitive subset.
Proof.
move=> x y z subxy subyz t.
move/subxy. (* bad explanation *)
move/subyz. (* bad explanation *)
by [].
Qed.

End Using_Definition.

Section Natural_Numbers.
Check nat. (* Natural numbers *)
Print nat. (* Natural numbers is an inductively defined object*)
Lemma three : S (S (S O)) = 3 /\ 2 = 0.+1.+1.
Proof.
by apply: conj.
Qed.

(**
fixpoint
with fixpoint structure, any inductive type can be 
used to define recursive functions (those with inductively
defined object as domain) and induction principles (predicates on 
inductively defined object 
*)

Definition pair := fun (x : nat) (y : bool) => (x,y).
Print pair.

Definition natadd := fix add1 (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | p.+1 => (add1 p m).+1
  end.
Print natadd.
Compute (natadd 1 2).

(* fix is an expression-leveled definition of recursive function,
in this example, natadd is the name of the function while add1 is a structure visited
recursively as a part of the natadd;
we will see a similar example in euclidean division
*)

Lemma concrete_plus : plus 16 64 = 80.
Proof.
(* simpl. *) 
by []. 
Qed.

(** 
simpl allows to execute the calculation of a function,
in this example plus
*)

Lemma concrete_plus2 : addn 16 64 = 80.
Proof.
Print addn.
simpl. (* no simpl plus *)
by [].
Qed.

Print mult.
Print muln. (* no simpl mult *)

Print le.
Check (le 1 3).
Check (leq 1 3).
(* le is an inductive type *)
Lemma concrete_le : le 1 3.
Proof.
Print Le.le_trans.
by apply: (Le.le_trans _ 2); apply: Le.le_n_Sn.
Qed.

Print leq.
(* leq is a function on nat *)

Lemma concrete_big_leq : 1 <= 3. (* coercion *)
Proof. by []. Qed.
Print concrete_le.
Print concrete_big_leq.
End Natural_Numbers.

Section Induction_naturals.
(** rules of using rewrite

rewrite <tactique>.
rewrite ?<tactique>. (uses the tactique 0tomore times)
rewrite [in LHS]<tactique>.
rewrite [in RHS]<tactique>. (use the tactique only on right hand side of the equation)
rewrite [exp pattern]<tactique>.
rewrite /=. (equivalent to simpl.)
rewrite /def. (unfold a definition)
rewrite -/def.
rewrite [pattern]/def.
rewrite -[exp to be replaced]/(exp to replace). 
rewrite {}Hyp. (use the Hypothesis and throw it)
rewrite -{}Hyp.
*)
Print nat_ind.
Lemma plus_commute : forall n1 m1, n1 + m1 = m1 + n1.
Proof.
elim=>[m1| n IHn m].
  by rewrite add0n addn0.
rewrite -[n.+1 + m]/(n + m).+1 IHn.
(**
how to understand this step?
*)
elim: m=> [|n0 IHn0].
  by rewrite add0n.
by rewrite -addnS.
Qed.

Section Induction_naturals.
Section Euclidean_division.
(**
goal of the section :
define the Euclidean division
prove the definition meets requirement of Euclidean division
prove the injection of Euclidean division
parametric inductive type
*)

(* 3.1 *)
(* 3.2 *)
(* 3.3 *)

(* Thanks to fixpoints any objects defined inductively 
can be used to define recursive functions and induction principles
*)
Definition edivn_rec d := fix loop (m q : nat) {struct m} := if m - d is m’.+1 then loop m’ q.+1 else (q, m).
End Euclidean_division.
