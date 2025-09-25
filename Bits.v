(********************************************************************************)
(*  Bits.v - Bitvector type and notations.                                      *)
(********************************************************************************)

Set Implicit Arguments.
Set Strict Implicit.

From Stdlib Require Export Zmod Program.
From Research Require Import Tactics.

Declare Scope bits_scope.
Delimit Scope bits_scope with bits.

(* Bitwise operations. *)
Notation "a =? b" := (@Zmod.eqb _ a b) (at level 70) : bits_scope.
Notation "x #[ i ]" := (Zmod.slice i (i+1) x) (at level 2, right associativity) : bits_scope.
Notation "x .[ hi , lo ]" := (Zmod.slice lo (hi+1) x) : bits_scope.
Notation "a ## b" := (Zmod.app b a) (at level 30, format "a ## b") : bits_scope.

(* Arithmetic operations. *)
Notation "x ^ y" := (Zmod.xor x y) (format "x ^ y") : bits_scope.
Notation "x - y" := (Zmod.sub x y) (format "x - y") : bits_scope.
Notation "x + y" := (Zmod.add x y) (format "x + y") : bits_scope.
Notation "x * y" := (Zmod.mul x y) (format "x * y") : bits_scope.
Notation "- x" := (Zmod.opp x) (format "- x") : bits_scope.

(* Numerals and literals. *)
Notation "# n" := (bits.of_Z _ n) (at level 9, format "# n") : bits_scope.
Notation "1" := Zmod.one : bits_scope.
Notation "0" := Zmod.zero : bits_scope.

(* Zero-extension helper: turn a bitvector `b` into a larger bitvector of
    width `m` by reinterpreting its unsigned value. *)
Definition zeroExtend {n : Z} (m : Z) : bits n -> bits m :=
  Eval cbv beta iota zeta delta [ Zmod.unsigned Zmod.of_Z ] in
      (@Zmod.of_Z (2 ^ m)) ∘ (@Zmod.unsigned (2 ^ n)).

(* Helper lemmas about zero-extension. *)
Lemma zeroExtend_of_Z : forall (n m : Z) (z : Z),
    (0 < m <= n)%Z -> bits.of_Z n z = zeroExtend n (bits.of_Z m z).
Admitted.

Global Hint Resolve zeroExtend_of_Z : bits_db.
