From stdpp Require Export base tactics list options.
From RecordUpdate Require Export RecordUpdate.

#[export] Set Printing Projections.

Ltac simplify := repeat progress (intros; simpl in *; list_simplifier; subst).
Ltac equality := intuition congruence.
