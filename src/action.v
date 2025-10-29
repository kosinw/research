From research Require Import base.

Set Warnings "-notation-for-abbreviation".
Set Asymmetric Patterns.

Section WithContext.
  Context {s : Type}.

  Definition Action (t : Type) := s -> t * s.

  Definition ret {t} (x : t) : Action t := fun s => (x, s).
  Definition bind {t1 t2} (m : Action t1) (f : t1 -> Action t2) :=
    fun r => let (x, s) := m r in (f x) s.

  Definition fmap {t1 t2} (m : Action t1) (f : t1 -> t2) :=
    bind m (fun x => ret (f x)).

  Definition pass : Action unit := ret tt.

  Definition get : Action s := fun s => (s, s).
  Definition put (x : s) : Action unit := fun _ => (tt, x).
  Definition modify (f : s -> s) : Action unit := fun s => (tt, f s).

  Definition runAction  {a} (m : Action a) (x : s) := m x.
  Definition runAction1 {a} (m : Action a) := (fst ∘ (runAction (a := a) m)).
  Definition runAction2 {a} (m : Action a) := (snd ∘ (runAction (a := a) m)).
End WithContext.

Notation ActionUnit := (Action unit).

Declare Scope action_scope.
Delimit Scope action_scope with action.

Infix ">>=" := bind (at level 60) : action_scope.
Infix ">>|" := fmap (at level 60) : action_scope.

Notation "'{{' e '}}'" := (e%action : Action _).

Notation "'let%bind' x ':=' e1 'in' e2" :=
  (e1 >>= (fun x => e2))%action
    (at level 100, x pattern, e2 at level 200, right associativity) : action_scope.

Notation "'let%map' x ':=' e1 'in' e2" :=
  (e1 >>| (fun x => e2))%action
    (at level 100, x pattern, e2 at level 200, right associativity) : action_scope.

Notation "'let%read' x ':=' e1 'in' e2" :=
  (get >>| e1 >>= (fun x => e2))%action
    (at level 100, x at next level, e2 at level 200, right associativity) : action_scope.

Notation "'let%write' x ':=' e1 'in' e2" :=
  (modify (set x (fun _ => e1)) >>= (fun _ => e2))%action
    (at level 100, x at next level, e2 at level 200, right associativity) : action_scope.

Notation "'let%modify' x ':=' e1 'in' e2" :=
  (modify (set x e1) >>= (fun _ => e2))%action
    (at level 100, x at next level, e2 at level 200, right associativity) : action_scope.

Notation "'let%call' x ':=' e1 'on' field 'in' e2" :=
  (get >>= (fun s =>
              let (x, s') := runAction e1 (field s) in
              put (set field (fun _ : _ => s') s) >>= (fun _ => e2)))%action
    (at level 100, x pattern, e1 at next level, field at next level,
      e2 at level 200, right associativity) : action_scope.

Notation " 'when' c 'then' e " := (if c then e else pass) (at level 200) : action_scope.
Notation " 'guard' c 'then' e " := (if c then e else pass) (at level 200) : action_scope.
