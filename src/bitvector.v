From stdpp Require Export base numbers bitvector.

Local Open Scope bv_scope.

#[export]
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section WithContext.
  Context {n : N}.

  Definition bv_eqb (x y : bv n) : bool :=
    Eval cbv beta iota zeta delta [ bool_decide decide_rel ] in
      bool_decide (x = y).

  Definition bv_odd (x : bv n) := Z.odd (bv_unsigned x).
End WithContext.


Infix "=?" := bv_eqb : bv_scope.
Infix "#" := bv_zero_extend (at level 65) : bv_scope.
Infix "||" := (bv_concat _) : bv_scope.
