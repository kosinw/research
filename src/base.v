(**********************************************************************************)
(*                                                                                *)
(*             base.v - Project base utilities and proof tactics.                 *)
(*                                                                                *)
(*  Provides:                                                                     *)
(*   - Re-exports common libraries used across the development.                   *)
(*   - Printing setting for record projections.                                   *)
(*   - Lightweight automation tactics [simplify] and [equality].                  *)
(*                                                                                *)
(**********************************************************************************)

From stdpp Require Export base tactics list options.
From RecordUpdate Require Export RecordUpdate.

#[export] Set Printing Projections.

Ltac simplify := repeat progress (intros; simpl in *; list_simplifier; subst).
Ltac equality := intuition congruence.
Ltac propositional := intuition.
