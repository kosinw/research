From research Require Import base.
From research Require Export action.
From stdpp Require Import option.

Class Circuit (t m tr : Type) :=
  { mkCircuit : t
  ; circuitResult : m -> Type
  ; circuitCall : forall (method : m), @Action t (circuitResult method)
  ; circuitTrace : t -> list tr
  }.

Definition circuitStep `(c : Circuit t m tr) (method : m) (state : t) : t :=
  default state (runAction2 (circuitCall method) state).

Definition circuitSteps `(c : Circuit t m tr) (ms : list m) (state : t) : t :=
  fold_left (fun st m => circuitStep c m st) ms state.

Definition runCircuit `(c : Circuit t m tr) (ms : list m) : t :=
  circuitSteps c ms mkCircuit.

Lemma circuitStepsApp `(c: Circuit t m tr) : forall xs1 xs2 st,
    circuitSteps c (xs1 ++ xs2) st =
      circuitSteps c xs2 (circuitSteps c xs1 st).
Proof.
  cbv [circuitSteps].
  intros ???.
  rewrite fold_left_app.
  equality.
Qed.

Lemma runCircuitApp `(c: Circuit t m tr) : forall xs1 xs2,
    runCircuit c (xs1 ++ xs2) =
      circuitSteps c xs2 (runCircuit c xs1).
Proof.
  cbv [runCircuit].
  intros ??.
  apply circuitStepsApp.
Qed.

Definition simulates
  `(c1: Circuit t1 m1 tr)
  `(c2: Circuit t2 m2 tr)
  policy
  (R : t1 -> t2 -> Prop) :=
  forall s1 s2,
    R s1 s2 ->
    (forall m s1' s2',
        s1' = circuitStep c1 m s1 ->
        s2' = circuitStep c2 (policy m) s2 ->
        R s1' s2').

Notation "c1 ∼ c2 : policy ; R" := (simulates c1 c2 policy R) (at level 60, c2 at next level).

(* We say a circuit [c] is constant time relevant to some policy [policy],
   if given the set of method calls to [c], we get the specification leakage
   by applying policy [policy] to the series of method calls. If from the specification
   leakage we can determine the implementation leakage trace, we get constant time
   wrt [policy]. *)
Definition constantTime {m2} `(c : Circuit t m1 tr) (policy : list m1 -> list m2) :=
  exists f, forall xs, circuitTrace (runCircuit c xs) = f (policy xs).

Lemma simulationConstantTime `(c1 : Circuit t1 m1 tr) `(c2 : Circuit t2 m2 tr) policy :
  forall R, (c1 ∼ c2 : policy; R) ->
       R c1.(mkCircuit) c2.(mkCircuit) ->
       (forall t1 t2, R t1 t2 -> c1.(circuitTrace) t1 = c2.(circuitTrace) t2) ->
       constantTime c1 (map policy).
Proof.
  intros R Hsimulates Hinit Htrace.
  cbv [ constantTime simulates ] in *.
  exists (fun zs => circuitTrace (runCircuit c2 zs)).
  intros.
  apply Htrace.
  induction xs using rev_ind.
  - assumption.
  - rewrite map_app.
    rewrite !runCircuitApp.
    simplify.
    apply Hsimulates with
      (s1 := runCircuit c1 xs)
      (s2 := runCircuit c2 (map policy xs))
      (m := x); equality.
Qed.

Arguments Circuit {_ _ _}.
