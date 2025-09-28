From stdpp Require Export base numbers bitvector.

Local Open Scope bv_scope.

#[export] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section WithContext.
  Context {n : N}.

  Definition bv_eqb (x y : bv n) : bool :=
    Eval cbv beta iota zeta delta [ bool_decide decide_rel ] in
      bool_decide (x = y).

  Definition bv_testbit (x : bv n) (i : Z) : bool :=
    Z.testbit (bv_unsigned x) i.

  Definition bv_odd (x : bv n) := Z.odd (bv_unsigned x).
End WithContext.


Infix "=?" := bv_eqb (only parsing) : bv_scope.
Infix "#" := bv_zero_extend (at level 35, only parsing) : bv_scope.
Infix "||" := (bv_concat _) (only parsing) : bv_scope.
Infix "!" := bv_testbit (at level 35, only parsing) : bv_scope.
