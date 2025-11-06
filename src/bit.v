From research Require Import base.
From stdpp Require Export bitvector.

Local Open Scope bv_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Definition Bit n := bv n.

Definition zeroExtend {n z} := bv_zero_extend (n := n) z.
Definition truncate {n z} := bv_zero_extend (n := n) z.
Definition signExtend {n z} := bv_sign_extend (n := n) z.
Definition concat {n n1 n2} := bv_concat n (n1 := n1) (n2 := n2).

Infix "++:" := concat (at level 60, right associativity) : bv_scope.

Definition truncate1 {n} := truncate (n := n) (z := 1).
