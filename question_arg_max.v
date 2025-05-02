From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Definition pick (T : finType) (P : pred T) := ohead (enum P).
Variable T : Type.
Implicit Type s : seq T.
Check ohead.
(* Ohead returns the type (option T) which is either None or Some x *)
Definition oseq s := if s is _ :: _ then s else nil. (* Zhan *)
Definition pickseq (T : finType) (P : pred T) := enum P. (* Zhan *)

Section Extrema.

Variant extremum_spec {T : eqType} (ord : rel T) {I : finType}
  (P : pred I) (F : I → T) : I → Type :=
  ExtremumSpec (i : I) of P i & (∀ j : I, P j → ord (F i) (F j)) :
                   extremum_spec ord P F i.

Let arg_pred {T : eqType} ord {I : finType} (P : pred I) (F : I → T) :=
  [pred i | P i & [forall (j | P j), ord (F i) (F j)]].

Section Extremum.

Context {T : eqType} {I : finType} (ord : rel T).
Context (i0 : I) (P : pred I) (F : I → T).

Definition extremum := odflt i0 (pick (arg_pred ord P F)).

Definition extremumseq := 
  if (enum (arg_pred ord P F)) is nil then (cons i0 nil) 
  else (enum (arg_pred ord P F)). (* Zhan *)

End Extremum.

Section ArgMinMax.

Variables (I : finType) (i0 : I) (P : pred I) (F : I → nat) (Pi0 : P i0).

Definition arg_min := extremum leq i0 P F.
Definition arg_max := extremum geq i0 P F.

Definition arg_max_seq := extremumseq geq i0 P F. (* Zhan *)

End ArgMinMax.

End Extrema.

(** 
another solution is possible by definition (Omega : {set O}) where O : finType

and to use maxset and to find the maximal set where every element in the set
could maximize the social welfare function, however more combinations would appear.

*)
Print maxset.

(** documentation:
https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html#Sequences.T
https://math-comp.github.io/htmldoc/mathcomp.ssreflect.fintype.html
https://math-comp.github.io/htmldoc/mathcomp.ssreflect.finset.html 
https://rocq-prover.org/doc/v8.9/stdlib/Coq.ssr.ssrbool.html#classically

*)
