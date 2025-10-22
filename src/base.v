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

From stdpp Require Export base tactics list vector options.
From RecordUpdate Require Export RecordUpdate.

#[export] Set Printing Projections.
#[export] Set Implicit Arguments.
#[export] Set Warnings "-notation-for-abbreviation".

Ltac simplify := repeat progress (intros; simpl in *; list_simplifier; subst).
Ltac equality := intuition congruence.
Ltac propositional := intuition.

Notation Maybe := @option.
Definition Valid {t} := Some (A := t).
Definition Invalid {t} := None (A := t).

Definition Bool := bool.
Definition Vector n t := Vector.t t n.
