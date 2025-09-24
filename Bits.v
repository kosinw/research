From Stdlib Require Export Zmod.

(**********************************************************************************)
(* Bit-level notations, all living in scope `bits_scope`.                         *)
(* - `x # n` constructs an n-bit value from integer x (mod 2^n).                  *)
(* - `a =? b` is bitvector equality.                                              *)
(* - `x #[ i ]` is the single-bit slice at index i.                               *)
(* - `x .[ hi , lo ]` is the inclusive slice from lo to hi.                       *)
(* - `a ++ b` concatenates `a` above `b` (note the argument order of `Zmod.app`). *)
(* - `+`, `-`, `*` are bitvector arithmetic modulo the bitwidth.                  *)
(**********************************************************************************)

Declare Scope bits_scope.
Delimit Scope bits_scope with bits.

Notation "x # n" := (Zmod.of_Z (2 ^ n) x) (at level 0, format "x # n") : bits_scope.
Notation "a =? b" :=
  (@Zmod.eqb _ a b) (at level 70) : bits_scope.
Notation "x #[ i ]" :=
  (Zmod.slice i (i+1) x)
    (at level 2, right associativity, format "x #[ i ]") : bits_scope.
Notation "x .[ hi , lo ]" :=
  (Zmod.slice lo (hi+1) x)
    (format "x .[ hi , lo ]") : bits_scope.
Notation "a ++ b" := (Zmod.app b a) (format "a ++ b") : bits_scope.
Notation "a + b" := (Zmod.add a b) (format "a + b") : bits_scope.
Notation "a - b" := (Zmod.sub a b) (format "a - b") : bits_scope.
Notation "a * b" := (Zmod.mul a b) (format "a * b") : bits_scope.

Notation "x ^ y" := (Zmod.pow x y) : bits_scope.
Notation "x - y" := (Zmod.sub x y) : bits_scope.
Notation "x + y" := (Zmod.add x y) : bits_scope.
Notation "x * y" := (Zmod.mul x y) : bits_scope.
Notation "1" := Zmod.one : bits_scope.
Notation "0" := Zmod.zero : bits_scope.
Notation "- x" := (Zmod.opp x) : bits_scope.

Bind Scope bits_scope with Zmod.

Local Open Scope bits_scope.

(* Zero-extension helper: turn a bitvector `b` into a larger bitvector of
    width `z` by reinterpreting its unsigned value. *)
Definition zext {n} (z : Z) (b : bits n) := (Zmod.unsigned b)#z.
