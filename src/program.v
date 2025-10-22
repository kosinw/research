From research Require Import base.

Set Warnings "-notation-for-abbreviation".
Set Asymmetric Patterns.

Section WithContext.
  Context {s : Type}.

  Definition ActionValue (t : Type) := s -> s * t.
  Definition Action := ActionValue unit.

  Definition ret {t} (x : t) : ActionValue t := fun s => (s, x).
  Definition bind {t1 t2} (m : ActionValue t1) (f : t1 -> ActionValue t2) :=
    fun r => let (s, x) := m r in (f x) s.

  Definition fmap {t1 t2} (m : ActionValue t1) (f : t1 -> t2) :=
    bind m (fun x => ret (f x)).

  Definition pass : ActionValue unit := ret tt.

  Definition get : ActionValue s := fun s => (s, s).
  Definition put (x : s) : ActionValue unit := fun _ => (x, tt).
  Definition modify (f : s -> s) : ActionValue unit := fun s => (f s, tt).

  Definition runAction {a} (m : ActionValue a) (x : s) := m x.
  Definition runAction1 {a} (m : ActionValue a) (x : s) := (runAction (a := a) m x).1.
  Definition runAction2 {a} (m : ActionValue a) (x : s) := (runAction (a := a) m x).2.
End WithContext.

Declare Scope action_scope.
Delimit Scope action_scope with action.

Notation "{{ e }}" := (e%action : ActionValue _).

Notation "x ;; z" :=
  (bind x%action (λ _, z%action))
    (at level 100, z at level 200, right associativity) : action_scope.

Notation "x <- y ;; z" :=
  (bind y%action (λ x : _, z%action))
    (at level 100, y at next level, z at level 200, right associativity) : action_scope.

Notation "m .:( f )" := (f ∘ m) : action_scope.

Infix ">>=" := bind (at level 60) : action_scope.

Infix ">>|" := fmap (at level 60) : action_scope.

Notation " '$' m " := (get >>| m)%action (at level 90) : action_scope.

Notation " 'when' c 'then' e " := (if c then e else pass) (at level 200) : action_scope.

Notation " f1 <=: v" :=
  (modify (set f1 (fun _ => v))) (at level 90) : action_scope.

Notation " f1 .:( f2 ) <=: v" :=
  (modify (set f1 (set f2 (fun _ => v)))) : action_scope.

Notation " f1 .:( f2 ) .:( f3 ) <=: v" :=
  (modify (set f1 (set f2 (set f3 (fun _ => v))))) : action_scope.

Notation " f1 .:( f2 ) .:( f3 ) .:( f4 ) <=: v" :=
  (modify (set f1 (set f2 (set f3 (set f4 (fun _ => v)))))) : action_scope.

Notation " f1 .:( f2 ) .:( f3 ) .:( f4 ) .:( f5 ) <=: v" :=
  (modify (set f1 (set f2 (set f3 (set f4 (set f5 (fun _ => v))))))) : action_scope.

Notation " L ↩ l " := (modify (set L (fun v => v ++ [l]))) (at level 40) : action_scope.

Notation "'begin' e 'end'" := (e) : action_scope.
