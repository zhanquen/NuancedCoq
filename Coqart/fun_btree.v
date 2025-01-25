From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.perm. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Compute_Fact.
(**
https://coq-community.org/coq-art/ch2_types_expressions/index.html
*)

(* how to define a function ? *)
(**
Mathcomp chap 1 <https://math-comp.github.io/mcb/>

Basic function: 

Definition <name> := fun <input> => <output>.
Definition <name> : <fun type> := fun <input> => <output>.
Definition <name> <parameter> := fun <input> => <output>.
Definition <name> (<parameter> : <para type>) : <fun type> := fun <input> => <output>.

We can choose a part of input as parameter.

Flow function:

Definition <name> <parameter> :=

  match <parameter> with
    <pattern1> => <output1>
    <pattern2> => <output2>
    ...
    <patternN> => <outputN>
  end.
  
in Flow function, the structure
  match <parameter> with
    <pattern1> => <output1>
    <pattern2> => <output2>
    ...
    <patternN> => <outputN>
  end
is considered in total as a return of the function, the part in front of the symbol "=>"
is the pattern, or control flow as a part of the return. we can combine it in the case
of multiple parameters

Definition same_bool b1 b2 :=
  match b1 with
  | true => match b2 with true => true | _ => false end
  | false => match b2 with true => false | _ => true end
  end.

*)
Check (fun n=>n+1). (* definition *)
Check ((fun n=>n+1) 2). (* application *)
Compute ((fun n=>n+1) 2). (* computation *)
Definition f : nat->nat := fun n=>n+1. (* nomination *)
Check f 2.
Compute f 2.
Definition f1 n := n + 1. (* parameterized nomination *)
Compute f1 2.
Definition h (n : nat) := fun m=>m+n*2.
Check h.
Compute (h 2 1).

Definition repeat_twice (g : nat -> nat) : nat -> nat := fun x => g (g x).
Check repeat_twice.
Compute repeat_twice f 2.

Definition three_patterns n :=

  match n with
    u.+1.+1.+1.+1.+1 => u
  | v.+1 => v
  | 0 => n
  end.
(* how to define a recursive function ? *)
Fixpoint fact (n : nat) :nat := 
  match n with
  | 0 => 1
  | p.+1 => n * fact(p)
  end.
  
Compute fact 5.
(** expected result : 
 = 120 : Z
*)

Example test_fact : fact 5 = 120.
Proof. reflexivity. Qed.


End Compute_Fact.


(**
Required libraries

Max 
  for computing the maximum of two numbers
  from mathcomp.ssreflect.ssrnat

int
  for using integer
  from mathcomp.algebra.ssrint
  https://github.com/math-comp/math-comp/blob/master/mathcomp/algebra/ssrint.v
bool
List
*)
From mathcomp Require Import algebra.ssrint. 
Section Binary_Tree.
Check int.
Inductive Zbtree : Type :=
|  leaf : Zbtree
|  bnode (r:int)(t1 t2: Zbtree).
Print Zbtree.
Print leaf.
Check leaf.
Variable (n: int).
Check (bnode n).
Check (0%Z).
Check (Negz 0).
Check ((-1)%Z).
Check (bnode (0%Z) leaf leaf).
(** Checks whether t is a leaf *)
Definition is_leaf (t: Zbtree) : bool :=
  match t with 
  | leaf => true
  | bnode m tl tr => false
  end.
Compute (is_leaf leaf).
Compute (is_leaf (bnode (0%Z) leaf leaf)).
End Binary_Tree.
