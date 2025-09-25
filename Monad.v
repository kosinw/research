(********************************************************************************)
(*  Monad.v - Typeclass which describes monads and state monads.                *)
(********************************************************************************)

Set Implicit Arguments.
Set Strict Implicit.

Class Monad (m : Type -> Type) : Type :=
  mk { ret : forall {A : Type}, A -> m A
     ; bind : forall {A B : Type}, m A -> (A -> m B) -> m B }.

Global Hint Mode Monad ! : typeclass_instances.

Definition liftM
  {m : Type -> Type} {M : Monad m} {T U : Type}
  (f : T -> U) : m T -> m U :=
  fun x => bind x (fun x => ret (f x)).

Definition liftM2
  {m : Type -> Type} {M : Monad m} {T U V : Type}
  (f : T -> U -> V) : m T -> m U -> m V :=
  Eval cbv beta iota zeta delta [ liftM ] in
    fun x y => bind x (fun x => liftM (f x) y).

Definition liftM3
  {m : Type -> Type} {M : Monad m} {T U V W : Type}
  (f : T -> U -> V -> W) : m T -> m U -> m V -> m W :=
  Eval cbv beta iota zeta delta [ liftM2 ] in
    fun x y z => bind x (fun x => liftM2 (f x) y z).

Definition kleisli
  {m : Type -> Type} {M : Monad m} {A B C : Type}
  (f : A -> m B) (g : B -> m C) : A -> m C :=
  fun a => bind (f a) g.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope.
Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 61, right associativity) : monad_scope.

(* Notation "f >=> g" := (@kleisli _ _ _ _ _ f g) (at level 61, right associativity) : monad_scope. *)
(* Notation "f <=< g" := (@kleisli _ _ _ _ _ g f) (at level 61, right associativity) : monad_scope. *)

Notation "e1 ;; e2" := (@bind _ _ _ _ e1%monad (fun _ => e2%monad))%monad
                         (at level 61, right associativity) : monad_scope.

Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
                              (at level 61, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

Definition StateM {State : Type} (A : Type) : Type := State -> (A * State).

Instance stateMonad {State : Type} : Monad StateM :=
  { ret := fun {A: Type} (a : A) => fun s => (a, s)
  ; bind := fun {A B : Type} (ma : (@StateM State A)) (f : A -> (@StateM State B)) =>
            fun s => let (a, s') := ma s in f a s' }.

Definition get {State : Type} : StateM State := fun s => (s, s).
Definition put {State : Type} (s : State) : StateM unit := fun _ => (tt, s).
