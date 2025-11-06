From research Require Import base.
From stdpp Require Import option.

Section WithContext.
  Context {s : Type}.

  Definition Action (t : Type) := s -> option (t * s).

  Definition ret {t} (x : t) : Action t := fun s => Some (x, s).

  Definition bind {t1 t2} (m : Action t1) (f : t1 -> Action t2) :=
    fun r =>
      match m r with
      | Some (x, s) => (f x) s
      | None => None
      end.

  Definition fmap {t1 t2} (m : Action t1) (f : t1 -> t2) :=
    Eval cbv [ bind ret ] in bind m (fun x => ret (f x)).

  Definition pass : Action unit := Eval cbv [ ret ] in ret tt.
  Definition fail {t} : Action t := fun _ => None.

  Definition get : Action s := fun s => Some (s, s).
  Definition put (x : s) : Action unit := fun _ => Some (tt, x).
  Definition modify (f : s -> s) : Action unit := fun s => Some (tt, f s).

  Definition guard {t} (b : s -> bool) (m : Action t) : Action t :=
    fun s => if b s then m s else fail s.

  Definition optionAction {t} (o : option t) : Action t :=
    Eval cbv [ option_map ] in
    fun s => option_map (fun x => (x, s)) o.

  Definition runAction {a} (m : Action a) (x : s) := m x.

  Definition nextState {a} (m : Action a) (st : s) :=
    Eval cbv [ option_map snd from_option compose runAction id ] in
    default st ((option_map snd ∘ (runAction (a := a) m)) st).
End WithContext.

Declare Scope action_scope.
Delimit Scope action_scope with action.
Local Open Scope action_scope.

Infix ">>=" := bind (at level 60) : action_scope.
Infix ">>|" := fmap (at level 60) : action_scope.

Definition read {s a} (getter : s -> a) : Action (s := s) a :=
  Eval cbv [ get fmap ] in
  get >>| getter.

Definition call {s a b}
  (getter : s -> a)
  (setter : a -> s -> s)
  (action : Action (s := a) b) : Action (s := s) b :=
  Eval cbv [ bind get runAction optionAction put ] in
  get >>= (fun st =>
    optionAction (runAction action (getter st)) >>= (fun '(x, st') =>
      put (setter st' st) >>| (fun _ => x))).

Notation "'{{' e '}}'" := (e%action).

Notation "'let%bind' x ':=' e1 'in' e2" :=
  (e1 >>= (fun x => e2))%action
    (at level 100, x pattern, e2 at level 200, right associativity) : action_scope.

Notation "'let%map' x ':=' e1 'in' e2" :=
  (e1 >>| (fun x => e2))%action
    (at level 100, x pattern, e2 at level 200, right associativity) : action_scope.

Notation "'let%read' x ':=' proj 'in' e2" :=
  (read proj >>= (fun x => e2))%action
    (at level 100, x at next level, e2 at level 200, right associativity) : action_scope.

(* TODO knwabueze: Maybe make %write and %modify return the prior value?? *)
Notation "'let%write' '_' ':=' e1 'on' proj 'in' e2" :=
  (modify (fun s => s <| proj := e1 |>) >>= (fun _ => e2))%action
    (at level 100, proj at next level, e2 at level 200, right associativity) : action_scope.

Notation "'let%modify' '_' ':=' e1 'on' proj 'in' e2" :=
  (modify (fun s => s <| proj ::= e1 |>) >>= (fun _ => e2))%action
    (at level 100, proj at next level, e2 at level 200, right associativity) : action_scope.

Notation "'let%call' x ':=' e1 'on' proj 'in' e2" :=
  (call proj (fun v s => s <| proj := v |>) e1 >>= (fun x => e2))%action
    (at level 100, x pattern, e1 at next level, proj at next level,
      e2 at level 200, right associativity) : action_scope.

Notation " 'when' c 'then' e " := (if c then e else pass) (at level 200) : action_scope.

Global Hint Unfold get put modify fmap bind ret : core.
Global Hint Unfold fail pass guard call read : core.
Global Hint Unfold runAction : core.
