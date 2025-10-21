From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section ArrowThm.

Variables (A : finType).

Variables (n'' : nat).

Definition n' := n''.+1.

Definition n := n'.+1.

Definition I := 'I_n.

Variables i : I.
(**
Variable (L : rel A) (trL : transitive L) (asL : antisymmetric L) (totL : total L).
*)
Record relL :=
  new {
    L : rel A;
    trL : transitive L;
    asL : antisymmetric L;
    totL : total L
  }.
  
Variables preference : I -> relL.

Check (preference i).
