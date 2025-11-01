From research Require Import base.
From research Require Export action.
From stdpp Require Import option.

Class Circuit (s m tr : Type) :=
  { mkCircuit : s
  ; circuitCall : m -> @Action s unit
  ; circuitTrace : s -> list tr
  }.

Definition circuitStep `(c : Circuit s m tr) (method : m) (state : s) : s :=
  nextState (circuitCall method) state.

Definition circuitSteps `(c : Circuit s m tr) (ms : list m) (state : s) : s :=
  fold_left (fun st m => circuitStep c m st) ms state.

Definition runCircuit `(c : Circuit s m tr) (ms : list m) : s :=
  circuitSteps c ms mkCircuit.

Lemma circuitStepsApp `(c: Circuit s m tr) : forall xs1 xs2 st,
    circuitSteps c (xs1 ++ xs2) st =
      circuitSteps c xs2 (circuitSteps c xs1 st).
Proof.
  cbv [circuitSteps].
  intros ???.
  rewrite fold_left_app.
  equality.
Qed.

Lemma runCircuitApp `(c: Circuit s m tr) : forall xs1 xs2,
    runCircuit c (xs1 ++ xs2) =
      circuitSteps c xs2 (runCircuit c xs1).
Proof.
  cbv [runCircuit].
  intros ??.
  apply circuitStepsApp.
Qed.

Definition simulates {s1 s2 t1 t2} a1 a2 (R : s1 -> s2 -> Prop) :=
  forall st1 st2,
    R st1 st2 ->
    (forall st1' st2',
        st1' = nextState (a := t1) a1 st1 ->
        st2' = nextState (a := t2) a2 st2 ->
        R st1' st2').

Notation "m1 ≺ m2 : R" := (simulates m1 m2 R) (at level 60, m2 at next level).

Definition circuitSimulates `(c1: Circuit s1 m1 tr) `(c2: Circuit s2 m2 tr) p R
  := forall m, c1.(circuitCall) m ≺ c2.(circuitCall) (p m) : R.

Notation "c1 ∼ c2 : policy ; R" :=
  (circuitSimulates c1 c2 policy R) (at level 60, c2 at next level).

(* We say a circuit [c] is constant time relevant to some policy [policy],
   if given the set of method calls to [c], we get the specification leakage
   by applying policy [policy] to the series of method calls. If from the specification
   leakage we can determine the implementation leakage trace, we get constant time
   wrt [policy]. *)
Definition constantTime {m2} `(c : Circuit s m1 tr) (policy : list m1 -> list m2) :=
  exists f, forall xs, circuitTrace (runCircuit c xs) = f (policy xs).

Lemma circuitConstantTime
  `(c1 : Circuit s1 m1 tr)
  `(c2 : Circuit s2 m2 tr) policy :
  forall R, (c1 ∼ c2 : policy; R) ->
       R c1.(mkCircuit) c2.(mkCircuit) ->
       (forall st1 st2, R st1 st2 -> c1.(circuitTrace) st1 = c2.(circuitTrace) st2) ->
       constantTime c1 (map policy).
Proof.
  intros R Hsimulates Hinit Htrace.
  cbv [ constantTime circuitSimulates simulates ] in *.
  exists (fun zs => circuitTrace (runCircuit c2 zs)).
  intros.
  apply Htrace.
  induction xs using rev_ind.
  - assumption.
  - rewrite map_app.
    rewrite !runCircuitApp.
    simplify.
    set (st1 := runCircuit c1 xs) in *.
    set (st2 := runCircuit c2 (map policy xs)) in *.
    apply Hsimulates with (st1 := st1) (st2 := st2) (m := x); equality.
Qed.

Arguments Circuit {_ _ _}.
