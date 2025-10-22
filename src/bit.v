(* *********************************************************************************)
(*                                                                                 *)
(*             bit.v - Bitvector helpers, notations, and lemmas.                   *)
(*                                                                                 *)
(***********************************************************************************)

From research Require Import base.
From stdpp Require Export bitvector.

Local Open Scope bv_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Definition Bit n := bv n.

Definition zeroExtend {n z} := bv_zero_extend (n := n) z.
Definition truncate {n z} := bv_zero_extend (n := n) z.
Definition signExtend {n z} := bv_sign_extend (n := n) z.
Definition concat {n n1 n2} := bv_concat n (n1 := n1) (n2 := n2).
Definition select {n1 n2} (h l : N) (b : Bit n1) : Bit n2 :=
  zeroExtend (Z_to_bv (h - l + 1) (b.(bv_unsigned) ≫ Z.of_N l)) : Bit n2.

Infix "++:" := concat (at level 60, right associativity) : bv_scope.
Notation "b [[ h ; l ]]" := (select h l b) : bv_scope.

Lemma bit_1_not_zero_then_one : forall (x : Bit 1), x <> 0 <-> x = 1.
Proof.
  induction x using bv_1_ind; equality.
Qed.

Lemma decide_bit1 (x : Bit 1) : {x = 0} + {x = 1}.
Proof.
  refine (
      if decide (x = 0) then _ else _
  ).
  - abstract (left; exact e).
  - abstract (right; apply bit_1_not_zero_then_one; exact n).
Qed.
