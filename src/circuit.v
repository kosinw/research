From research Require Import base.

(* A result corresponds to whether or not executing an action was aborted or
   not.

   You may also view a result as a set with either zero or one elements, where
   Failure corresponds to zero elements and Success coresponds to a singleton
   set. *)
Inductive Result s t :=
| Success : s -> t -> Result s t
| Failure : Result s t.

Hint Constructors Result : core.

Arguments Success {_ _}.
Arguments Failure {_ _}.

Local Instance resultElemOf {s t} : ElemOf (s * t) (Result s t) :=
  fun '(st, v) r =>
    match r with
    | Success st' v' => st = st' /\ v = v'
    | Failure => False
    end.

Local Instance emptyResult {s t} : Empty (Result s t) := Failure.

(** * The action monad *)

(* We will represent computations in a shallow embedding of Bluespec-style circuits by
   using state monads equipped with failure (also known as "guarded state monads").

   This will allow us to write imperative style programs for circuits without much hastle.

   The final target language will have sequential semantics as opposed to the serializable
   semantics between rules in Bluespec.
 *)
Definition Action s t := s -> Result s t.

(* Actions form a monad using the following two operators. *)
Definition ret {s t} (x : t) : Action s t := fun st => Success st x.

Definition bind {s t1 t2} (m : Action s t1) (f : t1 -> Action s t2) : Action s t2 :=
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

(* The following are standard operators for state monads. *)
Definition get {s} : Action s s := fun st => Success st st.

Definition put {s} (st : s) : Action s unit := fun _ => Success st tt.

Definition modify {s} (f : s -> s) : Action s unit := get >>= (fun st => put (f st)).

(* The following operators, [abort], [assert], and [guard], define what it means
   for an action to fail. *)
Definition abort {s t} : Action s t :=
  fun st => Failure.

Definition assert {s} (P : bool) : Action s unit :=
   if P then pass else abort.

Definition guard {s} (P : s -> bool) : Action s unit :=
  get >>= (fun st => assert (P st)).

(* [call] allows an action monad to call a different method given a submodule of [s]. *)
Definition call {s1 s2 t} (proj : s1 -> s2) (meth : Action s2 t)
  `{Setter (R := s1) (T := s2) proj} : Action s1 t :=
  get >>| proj >>=
    fun st2 =>
      match meth st2 with
      | Success st2' v => modify (set proj (fun _ => st2')) >>= const (ret v)
      | Failure => abort
      end.

Arguments call {_ _ _} (_) {_} (_).

(* Finally, we define what it means to run an action monad to the next state.

   Failure is equivalent to aborting a transaction, so the result is
   the same state plus some irrelevant value. *)
Definition run {s t} (m : Action s t) (st : s) :=
  match m st with
  | Success st' v => st'
  | Failure => st
  end.

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
      e2 at level 200, right associativity,
      only parsing).

Notation "'let%bind' x ':=' e1 'in' e2" :=
  (e1 >>= (fun x => e2))
    (at level 80, x pattern,
      e2 at level 200, right associativity,
      only parsing).

Notation "'let%map' x ':=' e1 'in' e2" :=
  (e1 >>| (fun x => e2))
    (at level 80, x pattern,
      e2 at level 200, right associativity,
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

Notation "m1 ';;' m2" := (m1 >>= (fun _ => m2)) (right associativity, only parsing).

Notation "'self' .( proj ) .( meth )" :=
  (call proj meth)
    (in custom call_expr, proj constr, meth constr, only parsing).

Notation "'let%call' x ':=' e1 'in' e2" :=
  (e1 >>= (fun x => e2))
    (at level 80, x pattern, e1 custom call_expr,
      only parsing).

Notation " 'when' c 'then' e " := (if c then e else pass) (at level 200).

(** * Hoare logic over action monads *)
Definition Assertion {s} := s -> Prop.

(* We can give partial correctness specifications to actions in the form of
   preconditions and postconditions to the execution of a particular action. *)
Definition hoareTriple {s t} (P : Assertion) (c : Action s t) (Q : t -> Assertion) :=
  forall st, P st -> forall st' v, (st', v) ∈ c st -> Q v st'.

Notation "{{ P }} c {{ Q }}" := (hoareTriple P c Q) (at level 90, c at next level).

Theorem hoareConsequence {s t} : forall  (c : Action s t) P Q P' Q',
    {{ P }} c {{ Q }}
    -> (forall st, P' st -> P st)
    -> (forall v st, Q v st -> Q' v st)
    -> {{ P' }} c {{ Q' }}.
Proof.
  cbv [ hoareTriple elem_of ].
  simplify.
  specialize H with (st := st).
  auto.
Qed.

Corollary hoareStrengthen {s t} : forall P (c : Action s t) Q Q',
    {{ P }} c {{ Q }} -> (forall v st, Q v st -> Q' v st) -> {{ P }} c {{ Q' }}.
Proof.
  simplify.
  eapply hoareConsequence; eauto.
Qed.

(** * Refinement *)
Class Refines A B := refines : A -> B -> Prop.
Infix "⊑" := refines.

Definition actionSimulates {s1 s2 t1 t2}
  (R : s1 -> s2 -> Prop) (m1 : Action s1 t1) (m2 : Action s2 t2) :=
  forall st1 st2 st2', R st1 st2 -> st2' = run m2 st2 ->
    exists st1', st1' = run m1 st1 /\ R st1' st2'.

Instance actionRefines {s1 t1 s2 t2} : Refines (Action s1 t1) (Action s2 t2) :=
  fun m1 m2 => exists (R : s1 -> s2 -> Prop), actionSimulates R m1 m2.

(* We can construct "circuit" objects for the purpose of verification properties
   such as showing refinement and stating theorems. *)
Definition Method (name : string) {s} arg res := arg -> Action s res.

Arguments Method : clear implicits.

Notation " 'method' name := body " :=
  (body : @Method name _ _ _)
    (at level 100, name at level 80).

Definition methodSimulates {name s1 s2 arg1 arg2 res1 res2}
  (R1 : s1 -> s2 -> Prop) (R2 : arg1 -> arg2 -> Prop)
  (m1 : Method name s1 arg1 res1) (m2 : Method name s2 arg2 res2) :=
  forall a1 a2, R2 a1 a2 -> actionSimulates R1 (m1 a1) (m2 a2).

Instance methodRefines {name s1 s2 arg1 arg2 res1 res2} :
  Refines (Method name s1 arg1 res1) (Method name s2 arg2 res2) :=
  fun m1 m2 => exists (R1 : s1 -> s2 -> Prop) (R2 : arg1 -> arg2 -> Prop),
      methodSimulates R1 R2 m1 m2.

Inductive Methods {s} : list string -> Type :=
| MethodsNil  : Methods []
| MethodsCons : forall name arg res (m : Method name s arg res) {names},
    Methods names -> Methods (name :: names).

Hint Constructors Methods : core.

Arguments Methods : clear implicits.

Notation "';' m1 ';' .. ';' mn" :=
  (MethodsCons m1 (.. (MethodsCons mn MethodsNil) ..)) (at level 101).

Inductive methodsSimulates {s1 s2} (R : s1 -> s2 -> Prop) :
  forall {names}, Methods s1 names -> Methods s2 names -> Prop :=
| MsNil : methodsSimulates R MethodsNil MethodsNil
| MsCons :
  forall {name arg1 arg2 res1 res2 names}
    (m1 : Method name s1 arg1 res1) (m2 : Method name s2 arg2 res2)
    (ms1 : Methods s1 names) (ms2 : Methods s2 names)
    (R2 : arg1 -> arg2 -> Prop),
    methodSimulates R R2 m1 m2 ->
    methodsSimulates R ms1 ms2 ->
    methodsSimulates R (MethodsCons m1 ms1) (MethodsCons m2 ms2).

Hint Constructors methodsSimulates : core.

Instance methodsRefines {s1 s2 names} : Refines (Methods s1 names) (Methods s2 names) :=
  fun ms1 ms2 => exists (R : s1 -> s2 -> Prop), methodsSimulates R ms1 ms2.

Record Circuit {names : list string} :=
  { circuitState : Type
  ; circuitEvent : Type
  ; circuitTrace : circuitState -> list circuitEvent
  ; circuitConstructor : circuitState
  ; circuitMethods : Methods circuitState names
  }.

Arguments Circuit : clear implicits.

Notation "{{ 'self' := state ';' 'trace' := trace ';' 'constructor' := constr ms }}" :=
  {| circuitState := state;
    circuitEvent := _;
    circuitTrace := trace;
    circuitConstructor := constr;
    circuitMethods := ms |}.

Record circuitSimulates {names} (c1 c2 : Circuit names)
  (R : circuitState c1 -> circuitState c2 -> Prop) : Prop :=
  { crConstructors : R (circuitConstructor c1) (circuitConstructor c2)
  ; crMethods : methodsSimulates R (circuitMethods c1) (circuitMethods c2)
  }.

Instance circuitRefines {names} : Refines (Circuit names) (Circuit names) :=
  fun c1 c2 => exists R, circuitSimulates c1 c2 R.

Definition counter1 : Circuit _ :=
  {{ self           := nat
   ; trace          := const (@nil unit)
   ; constructor    := 0
   ; method "val"   := fun _ : () => get
   ; method "incr1" := fun _ : () => modify S
   ; method "incr2" := fun _ : () => modify S
   ; method "reset" := fun _ : () => put 0
  }}.

Record Counter := { c1 : nat ; c2 : nat }.
Definition mkCounter := {| c1 := 0 ; c2 := 0 |}.
Definition counterVal := let%read c1 := self.(c1) in let%read c2 := self.(c2) in ret (c1 + c2).
Definition counterIncr1 := self.(c1) ::= S.
Definition counterIncr2 := self.(c2) ::= S.
Definition counterRst := self.(c1) := 0 ;; self.(c2) := 0.

Definition counter2 : Circuit _ :=
  {{ self           := Counter
   ; trace          := const (@nil unit)
   ; constructor    := mkCounter
   ; method "val"   := fun _ : () => counterVal
   ; method "incr1" := fun _ : () => counterIncr1
   ; method "incr2" := fun _ : () => counterIncr2
   ; method "reset" := fun _ : () => counterRst
  }}.

Ltac choose_relation R :=
  match goal with
  | [ |- ?a ⊑ ?b ] => exists R
  | [ |- methodsSimulates _ _ _ ] =>
      eapply MsCons with (R2 := R);
      cbv [ methodSimulates actionSimulates ];
      [ eexists | .. ]
  end; simplify.

Lemma counterRefines : counter2 ⊑ counter1.
Proof.
  choose_relation (fun st1 st2 => st1.(c1) + st1.(c2) = st2).
  split.
  equality.
  choose_relation (fun '() '() => True).
  equality.
  choose_relation (fun '() '() => True).
  equality.
  choose_relation (fun '() '() => True).
  propositional.
  choose_relation (fun '() '() => True).
  equality.
  constructor.
Qed.
