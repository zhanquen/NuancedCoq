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
Definition t1 := leaf.
Definition t2 : Zbtree := (bnode (0%Z) leaf leaf).
Definition t3 : Zbtree := (bnode ((-1)%Z) t1 t2).

Definition is_leaf (t: Zbtree) : bool :=
  match t with 
  | leaf => true
  | bnode m tl tr => false
  end.
Compute (is_leaf leaf).
Compute (is_leaf (bnode (0%Z) leaf leaf)).
(** Returns the total number of nodes (binary nodes and leaves) of t *)
Fixpoint size (t: Zbtree) : nat :=
  match t with
  | leaf => 1
  | bnode _ tl tr => ((size tl) + (size tr)).+1
  end.
Compute (size leaf).
Compute (size (bnode (0%Z) leaf leaf)).
Compute (size t3).
(** returns the heigth of t *)
Fixpoint height (t:Zbtree) : nat := 
  match t with
  | leaf => 0
  | bnode _ tl tr => (max (height tl) (height tr)).+1
  end.
Compute (height t1).
Compute (height t2).
Compute (height t3).
(** returns the mirror of t *)
Fixpoint mirror (t:Zbtree) : Zbtree :=
  match t with
  | leaf => leaf
  | bnode m tl tr => (bnode m (mirror tr) (mirror tl))
  end.
Compute (mirror t1).
Compute (mirror t2).
Print t3.
Compute (mirror t3).

(** Checks whether n labels some node of t *)
Fixpoint memb (n : int)(t: Zbtree) : bool :=
  match t with
  | leaf => false
  | bnode m tl tr => ((m == n) || (memb n tl) ||(memb n tr))
  end.
Compute (memb ((-1)%Z) t1).
Compute (memb ((-1)%Z) t2).
Compute (memb ((-1)%Z) t3).
Compute (memb (0%Z) t1).
Compute (memb (0%Z) t2).
Compute (memb (0%Z) t3).
Compute (memb (1%Z) t1).
Compute (memb (1%Z) t2).
Compute (memb (1%Z) t3).

(** Computes the list of t's labels (in infix order) *)
(* operations on the list: mechanism and operations *)
Inductive my_list: Type :=
  | nil: my_list
  | cons: nat -> my_list -> my_list.
Print my_list.
Compute (cons 0 nil).
Compute (cons 1 (cons 2 (cons 3 nil))).
Check (cons 1 (cons 2 (cons 3 nil))).
Definition trois : my_list := (cons 1 (cons 2 (cons 3 nil))).
Print trois.

Definition head (l:my_list) : nat :=
  match l with nil => 0
    | cons t q => t
  end.
  
Definition tail (l:my_list) : my_list:=
  match l with nil => nil
    | cons t q => q
  end.
Compute (head trois).
Compute (tail trois).
Theorem tete_trois_vaut_1 : (head trois) = 1.
Proof.
rewrite /trois.
by simpl. (* computable *)
Qed.

Fixpoint length (l:my_list) : nat :=
  match l with nil => 0
    | cons m l1 => S (length l1)
  end.
  
Theorem length_1: length trois = 3.
Proof.
rewrite /trois.
by simpl.
Qed.
Theorem length_2: length (tail trois) = 2.
Proof.
rewrite /trois /tail.
by simpl.
Qed.

Theorem rec_length (l : my_list) : ~(l = nil) -> ((length l) = (length (tail l)).+1).
Proof.
move=> notnil.
have lengthnotzero : 0 < (length l).
Admitted.
move: notnil.
case.
(* !!! document it with library *)
Fixpoint infix_list (t:Zbtree) : list int :=
  
End Binary_Tree.
