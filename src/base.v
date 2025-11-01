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

From stdpp Require Export base tactics list vector option options.
From RecordUpdate Require Export RecordUpdate.

#[export] Set Printing Projections.
#[export] Set Implicit Arguments.
#[export] Set Warnings "-notation-for-abbreviation".

Ltac simplify :=
  repeat progress (simpl in *; intros; autounfold with core in *; list_simplifier; subst).

Ltac equality := intuition congruence.
Ltac propositional := intuition.

Class Default A := default: A.
Global Hint Mode Default ! : typeclass_instances.
Notation "'δ'" := default (at level 0, format "δ").

Global Instance default_inhabited `(Default A) : Inhabited A := populate δ.

Instance bool__Default : Default bool := false.
Instance nat__Default : Default nat := 0.
Instance Z__Default : Default Z := 0%Z.
