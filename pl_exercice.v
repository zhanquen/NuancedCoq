From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.perm. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(* something interesting and worth reading *)
Section Lambda_Representation.
(* 1.2 表达式优先级 *)
Definition f2 := fun y : nat => (fun z : nat => y + z).
Print f2.

(* 1.3 约束变元改名公理 *)
Definition f31 := fun x : nat => (fun z : nat => x + z).
Print f31.
Definition f32 := fun z : nat => (fun z : nat => z + z).
Print f32.
Compute (f32 3 1).
(**
对于f2,
项(fun z : nat => y + z)有约束变量z和自由变量y,
项f2有约束变量z和约束变量y。

对于f32,
项(fun z : nat => z + z)有约束变量z。

在f2中，
由于z是项(fun z : nat => y + z)的约束变量，将项(fun z : nat => y + z)的自由变量y改为z
不符合约束变元改名公理
*)

(* 1.4 beta等价公理和beta规约 *)
Definition f4 := (fun f : (nat -> nat) => (f 10)) (fun x : nat => (x+x)).
Definition f41 := ((fun x : nat => (x+x)) 10). (* [(fun x : nat => (x+x))/f](fun f : (nat -> nat) => (f 10)) *)
Definition f42 := (10 + 10). (* [10/x](fun x : nat => (x+x)) *)
Compute f4.
Compute f41.
Compute f42.
End Lambda_Representation.
