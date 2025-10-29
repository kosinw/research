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
Notation Valid := (@Some _).
Notation Invalid := (@None _).
Notation Bool := bool.
Notation Vector := vec.

Definition snoc {A} (x : A) (l : list A) := l ++ [x].

Fixpoint mkVector {t} (zero : t) n {struct n} : Vector t n :=
  match n with
  | 0 => vnil
  | S n => zero ::: mkVector zero n
  end.
