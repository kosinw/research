From research Require Import base bit program simulates.

Notation Maybe := @option.

Inductive spec := | Spec__Enq (a : Bit 4) | Spec__Deq | Spec__Tick.
Inductive impl := | Impl__Enq | Impl__Deq | Impl__Tick.
Inductive method := | Method__Enq (a b : Bit 4) | Method__Deq | Method__Tick.
Inductive state := State__Empty | State__Busy | State__Full.
Instance state__EqDecision : EqDecision state. solve_decision. Defined.

Definition policy m :=
  match m with
  | Method__Enq a b => Spec__Enq a
  | Method__Deq => Spec__Deq
  | Method__Tick => Spec__Tick
  end.

Module Impl.
  Record t_inner :=
    { a : Bit 4
    ; b : Bit 4
    ; c : Bit 2
    ; p : Bit 8
    ; st : state
    ; trace : list impl
    }.

  Definition t := t_inner.

  Definition mk : t :=
    {| a := 0%bv
    ; b := 0%bv
    ; c := 0%bv
    ; p := 0%bv
    ; st := State__Empty
    ; trace := []
    |}.

  Definition enq in1 in2 :=
    {{ st' <- $st ;;
       when (decide (st' = State__Empty)) then
         trace ↩ Impl__Enq ;;
         a <=: in1 ;;
         b <=: in2 ;;
         c <=: 0%bv ;;
         p <=: 0%bv ;;
         st <=: State__Busy
    }}.

  Definition deq :=
    {{ st' <- $st ;;
       if (decide (st' = State__Full)) then
         trace ↩ Impl__Deq ;;
         st <=: State__Empty ;;
         p' <- $p ;;
         ret (Valid p')
       else
         ret Invalid
    }}.

  Definition shift_and_add :=
    {{ a' <- $a ;;
       b' <- $b ;;
       c' <- $c ;;
       p' <- $p ;;
       when decide (a' <> 0%bv) then
         let t :=
           if decide ((truncate a' : Bit 1) = 1)%bv then
             (zeroExtend b' : Bit 8)%bv
           else
             0%bv
         in
         p <=: (p' + (t ≪ (zeroExtend c' : Bit 8)))%bv ;;
         a <=: (a' ≫ 1)%bv ;;
         c <=: (c' + 1)%bv
    }}.

  Definition tick :=
    {{ st' <- $st ;;
       when (decide (st' = State__Busy)) then
         trace ↩ Impl__Tick ;;
         a' <- $a ;;
         if (decide (a' = 0%bv)) then
           st <=: State__Full
         else
           shift_and_add
    }}.

  Definition methodResult m :=
    match m with
    | Method__Enq _ _ => unit
    | Method__Deq => Maybe (Bit 8)
    | Method__Tick => unit
    end.

  Definition runMethod m : ActionValue (methodResult m) :=
    match m with
    | Method__Enq a b => enq a b
    | Method__Deq => deq
    | Method__Tick => tick
    end.

  Definition runMethod1 m := runAction1 (runMethod m).
  Definition runMethods xs := fold_left (fun a b => runMethod1 b a) xs.

  Definition circuit : Circuit t method := {| init := mk; run := runMethod1 |}.
End Impl.

Module Spec.
  Record t_inner :=
    { st : state
    ; a : Bit 4
    ; trace : list impl
    }.

  Definition t := t_inner.

  Definition mk : t :=
    {| st := State__Empty
    ; a := 0%bv
    ; trace := []
    |}.

  Definition enq in1 :=
    {{ st' <- $st ;;
       when (decide (st' = State__Empty)) then
         trace ↩ Impl__Enq ;;
         a <=: in1 ;;
         st <=: State__Busy
    }}.

  Definition deq :=
    {{ st' <- $st ;;
       when (decide (st' = State__Full)) then
         trace ↩ Impl__Deq ;;
         st <=: State__Empty
    }}.

  Definition shift :=
    {{ a' <- $a ;;
       when decide (a' <> 0%bv) then
         a <=: (a' ≫ 1)%bv
    }}.

  Definition tick :=
    {{ st' <- $st ;;
       when (decide (st' = State__Busy)) then
         trace ↩ Impl__Tick ;;
         a' <- $a ;;
         if (decide (a' = 0%bv)) then
           st <=: State__Full
         else
           shift
    }}.

  Definition specResult m :=
    match m with
    | Spec__Enq _ => unit
    | Spec__Deq => unit
    | Spec__Tick => unit
    end.

  Definition runSpec m : ActionValue (specResult m) :=
    match m with
    | Spec__Enq a => enq a
    | Spec__Deq => deq
    | Spec__Tick => tick
    end.

  Definition runSpec1 m := runAction1 (runSpec m).
  Definition runSpecs xs := fold_left (fun a b => runSpec1 b a) xs.

  Definition circuit : Circuit t spec := {| init := mk; run := runSpec1 |}.
End Spec.

Definition invariant s1 s2 :=
  s1.(Impl.st) = s2.(Spec.st) /\
    s1.(Impl.a) = s2.(Spec.a) /\
    s1.(Impl.trace) = s2.(Spec.trace).

Ltac t0 :=
  match goal with
  | t : Spec.t_inner |- _ => destruct t
  | t : Impl.t_inner |- _ => destruct t
  | m : method |- _ => destruct m
  | s : spec |- _ => destruct s
  | st : state |- _ => destruct st
  | |- context [ decide _ ] => case_decide
  | H : _ /\ _ |- _ => destruct_and! H
  | |- _ /\ _ => split
  end.

Ltac t1 :=
  unfold refines, bind, fmap, modify,
    get, runAction1, runAction,
    Impl.enq, Spec.enq, Impl.deq, Spec.deq,
    Impl.tick, Spec.tick, Impl.shift_and_add, Spec.shift,
    Impl.runMethod1, Spec.runSpec1, Impl.runMethod, Spec.runSpec,
    Impl.runMethods, Spec.runSpecs, runAction in *.

Ltac t2 := t1; simplify; t1; repeat (t0; simplify).
Ltac t := t2; try (equality || eauto 7).

Lemma enq_ok : forall s1 s2 a b,
    invariant s1 s2 ->
    invariant (runAction1 (Impl.enq a b) s1)
      (runAction1 (Spec.enq a) s2).
Proof.
  unfold invariant in *; t.
Qed.

Lemma deq_ok : forall s1 s2,
    invariant s1 s2 ->
    invariant (runAction1 Impl.deq s1)
      (runAction1 Spec.deq s2).
Proof.
  unfold invariant in *; t.
Qed.

Lemma tick_ok : forall s1 s2,
    invariant s1 s2 ->
    invariant (runAction1 Impl.tick s1)
      (runAction1 Spec.tick s2).
Proof.
  unfold invariant in *; t.
Qed.

Local Hint Resolve enq_ok deq_ok tick_ok : core.

Theorem refines_ok : refines Impl.circuit Spec.circuit policy invariant.
Proof.
  t.
Qed.

Local Hint Resolve refines_ok : core.

Lemma invariant_start : invariant Impl.mk Spec.mk.
Proof.
  unfold invariant in *; t.
Qed.

Local Hint Resolve invariant_start : core.

Corollary simulates_ok : policy ⊢ Impl.circuit ⊑ Spec.circuit.
Proof.
  unfold simulates in *; exists invariant; t.
Qed.

Local Hint Resolve simulates_ok : core.

Lemma runMethods_invariant : forall xs,
    invariant (Impl.runMethods xs Impl.mk)
      (Spec.runSpecs (map policy xs) Spec.mk).
Proof.
  induction xs using rev_ind.
  - t.
  - t1. rewrite map_app. repeat rewrite fold_left_app. eauto.
Qed.

Local Hint Resolve runMethods_invariant : core.

Theorem ct : exists f, forall xs s,
    s = Impl.runMethods xs Impl.mk ->
    s.(Impl.trace) = f (map policy xs).
Proof.
  exists (fun xs => (Spec.runSpecs xs Spec.mk).(Spec.trace)); intros;
  pose proof (runMethods_invariant xs); unfold invariant in *; t.
Qed.
