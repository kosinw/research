From research Require Import base.
From stdpp Require Export bitvector.

Local Open Scope bv_scope.

(* This allows automation tactics such as [bv_solve] to assume lia can handle
   `mod` and `div`. *)
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Definition bv_eqb {n} (x y : bv n) : bool :=
  Eval cbv delta [ bool_decide decide_rel ] in
    bool_decide (x = y).

Definition bv_odd {n} (x : bv n) := Z.odd (bv_unsigned x).

Infix "=?" := bv_eqb : bv_scope.
Infix "#" := bv_zero_extend (at level 65) : bv_scope.
Infix "||" := (bv_concat _) : bv_scope.
Notation "x ?" := (bv_odd x) : bv_scope.

Lemma bv_eqb_eq {n} : forall (x y : bv n), (x =? y) = true <-> x = y.
Proof.
  intuition; simplify.
  - unfold bv_eqb in *. destruct (bv_eq_dec n x y); equality.
  - unfold bv_eqb. destruct (bv_eq_dec n y y); equality.
Qed.

Lemma bv_eqb_neq {n} : forall (x y : bv n), (x =? y) = false <-> x <> y.
Proof.
  intuition; simplify.
  - unfold bv_eqb in *. destruct (bv_eq_dec n y y); equality.
  - unfold bv_eqb. destruct (bv_eq_dec n x y); equality.
Qed.

Lemma bv_not_zero_one : forall (x : bv 1), x <> 0 <-> x = 1.
Proof.
  simplify.
  assert (x = 0 \/ x = 1).
  { apply bv_1_ind with (P := (fun x => x = 0 \/ x = 1)); equality. }
  split; simplify.
  - destruct_or!; equality.
  - destruct_or!; equality.
Qed.

Lemma bv_not_one_zero : forall (x : bv 1), x <> 1 <-> x = 0.
Proof.
  simplify.
  assert (x = 0 \/ x = 1).
  { apply bv_1_ind with (P := (fun x => x = 0 \/ x = 1)); equality. }
  split; simplify.
  - destruct_or!; equality.
  - destruct_or!; equality.
Qed.

Ltac simplify_bv_eqb :=
  repeat progress (
      match goal with
      | H: (?x =? 0) = true |- _ => rewrite bv_eqb_eq in H
      | H: (?x =? 1) = true |- _ => rewrite bv_eqb_eq in H
      | H: (?x =? 0) = false |- _ => rewrite bv_eqb_neq in H
      | H: ?x <> 0 |- _ => rewrite bv_not_zero_one in H
      | H: (?x =? 1) = false |- _ => rewrite bv_eqb_neq in H
      | H: ?x <> 1 |- _ => rewrite bv_not_one_zero in H
      end
    ).
