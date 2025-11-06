From research Require Import base.

Inductive ActionResult s t :=
| Success : s -> t -> ActionResult s t
| Failure : ActionResult s t.

Arguments Success {_ _}.
Arguments Failure {_ _}.

Definition Action s t := s -> ActionResult s t.

Definition ret {s t} (x : t) : Action s t := fun st => Success st x.

Definition bind {s t1 t2} (m : Action s t1) (f : t1 -> Action s t2) :=
  fun st =>
    match m st with
    | Success st' v1 => (f v1) st'
    | Failure => Failure
    end.

Infix ">>=" := bind (at level 80, only parsing).

Definition lift {s t1 t2} (f : t1 -> t2) (m : Action s t1) : Action s t2 :=
  m >>= (fun x => ret (f x)).

Notation "m >>| f" := (lift f m) (at level 80, only parsing).

Definition pass {s} : Action s unit := ret tt.

Definition abort {s t} : Action s t :=
  fun st => Failure.

Definition assert {s} (predicate : s -> bool) : Action s unit :=
  fun st => if predicate st then pass st else abort st.

Definition get {s} : Action s s := fun st => Success st st.

Definition put {s} (st : s) : Action s unit := fun _ => Success st tt.

Definition modify {s} (f : s -> s) : Action s unit := get >>= (fun st => put (f st)).

Definition run {s t} `{Inhabited t} (m : Action s t) (st : s) :=
  match m st with
  | Success st' v => (st', v)
  | Failure => (st, δ)
  end.

Definition call {s1 s2 t} (proj : s1 -> s2) (meth : Action s2 t)
  `{Setter (R := s1) (T := s2) proj} : Action s1 t :=
  get >>| proj >>=
    fun st2 =>
      match meth st2 with
      | Success st2' v => modify (set proj (fun _ => st2')) >>= const (ret v)
      | Failure => abort
      end.

Arguments call {_ _ _} (_ _) {_} (_).

Declare Custom Entry bind_expr.
Declare Custom Entry call_expr.

Notation "'self'" :=
  get (in custom bind_expr, only parsing).

Notation "m .( proj )" :=
  (m >>| proj)
    (in custom bind_expr, proj constr, only parsing).

Notation "'let%read' x ':=' e1 'in' e2" :=
  (e1 >>= (fun x => e2))
    (at level 80, x pattern, e1 custom bind_expr,
      only parsing).

Notation "'let%bind' x ':=' e1 'in' e2" :=
  (e1 >>= (fun x => e2))
    (at level 80, x pattern, only parsing).

Notation "'let%map' x ':=' e1 'in' e2" :=
  (e1 >>| (fun x => e2))
    (at level 80, x pattern, e1 custom bind_expr,
      only parsing).

Notation "'self' ':=' e1" :=
  (put e1)
    (at level 200, e1 at level 80, only parsing).

Notation "'self' '::=' e1" :=
  (modify e1)
    (at level 200, e1 at level 80, only parsing).

Notation "'self' .( proj ) ':=' e1" :=
  (modify (set proj (fun _ => e1)))
    (at level 200, e1 at level 80, only parsing).

Notation "'self' .( proj ) '::=' e1" :=
  (modify (set proj e1))
    (at level 200, e1 at level 80, only parsing).

Notation "m1 ';;' m2" := (m1 >>= (fun _ => m2)) (only parsing).

Notation "'self' .( proj ) .( meth )" :=
  (call proj meth)
    (in custom call_expr, proj constr, meth constr, only parsing).

Notation "'let%call' x ':=' e1 'in' e2" :=
  (e1 >>= (fun x => e2))
    (at level 80, x pattern, e1 custom call_expr,
      only parsing).

Notation " 'when' c 'then' e " := (if c then e else pass) (at level 200).

Definition hoare_triple {s t} (P : s -> Prop) (c : Action s t) (Q : t -> s -> Prop) := forall st,
    P st ->
    match c st with
    | Success st' v => Q v st'
    | Failure => True
    end.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level).

Theorem hoare_consequence {s t} : forall P (c : Action s t) Q P' Q',
    {{ P }} c {{ Q }}
    -> (forall st, P' st -> P st)
    -> (forall v st, Q v st -> Q' v st)
    -> {{ P' }} c {{ Q' }}.
Proof.
  cbv [ hoare_triple ].
  intros.
  specialize H with (st := st).
  case_match; auto.
Qed.

Corollary hoare_strengthen {s t} : forall P (c : Action s t) Q Q',
    {{ P }} c {{ Q }} -> (forall v st, Q v st -> Q' v st) -> {{ P }} c {{ Q' }}.
Proof.
  simplify.
  eapply hoare_consequence; eauto.
Qed.

Record Method {s} a t :=
  { methodName : string
  ; methodBody : a -> Action s t
  }.

Notation " 'method' name ' x = body " :=
  {| methodName := name; methodBody := (fun x => body) |}
    (at level 100, x pattern).

Inductive Methods {s} : list string -> Type :=
| MethodsNil : Methods []
| MethodsCons : forall a t (m : Method (s := s) a t) {names},
    Methods names
    -> Methods (methodName (s := s) (a := a) m :: names).

Arguments Methods : clear implicits.

Record Circuit {names : list string} :=
  { circuitState : Type
  ; circuitConstructor : circuitState
  ; circuitMethods : Methods circuitState names
  }.

Arguments Circuit : clear implicits.

Notation "{{ 'rep' = state 'and' 'constructor' = constr ms }}" :=
  {| circuitState := state;
    circuitConstructor := constr;
    circuitMethods := ms |}.

Notation "'and' m1 'and' .. 'and' mn" :=
  (MethodsCons m1 (.. (MethodsCons mn MethodsNil) ..)) (at level 101).

Definition counter :=
  {{ rep = nat
     and constructor = 0
     and method "increment" '() = self ::= S
  }}.

Eval vm_compute in counter.(circuitMethods).
