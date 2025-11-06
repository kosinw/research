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

From stdpp Require Export base tactics list vector option strings options.
From RecordUpdate Require Export RecordUpdate.

#[export] Set Printing Projections.
#[export] Set Implicit Arguments.
#[export] Set Default Goal Selector "1".
#[export] Set Warnings "-notation-for-abbreviation".

Ltac simplify :=
  repeat progress (simpl in *; intros; autounfold with core in *; list_simplifier).

Ltac equality := intuition congruence.
Ltac propositional := intuition.

Notation δ := inhabitant.
