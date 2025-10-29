From research Require Import base bit circuit.

Notation Maybe := @option.

Inductive specLeakage :=
| SpecLeakage__Enq (a : Bit 4)
| SpecLeakage__Deq
| SpecLeakage__Rule.

Inductive implLeakage :=
| ImplLeakage__Enq
| ImplLeakage__Deq
| ImplLeakage__Rule.

Inductive method :=
| Enq (a b : Bit 4)
| Deq
| Rule.

Inductive state :=
| State__Empty
| State__Busy
| State__Full.

Instance state__EqDecision : EqDecision state. solve_decision. Defined.

Module Multiplier.
  Record t :=
    { a : Bit 4
    ; b : Bit 4
    ; c : Bit 2
    ; p : Bit 8
    ; st : state
    ; trace : list implLeakage
    }.

  Definition mk :=
    {| a := 0%bv
    ; b := 0%bv
    ; c := 0%bv
    ; p := 0%bv
    ; st := State__Empty
    ; trace := []
    |}.

  Definition enq in__a in__b :=
    {{ let%read st0 := st in
       guard decide (st0 = State__Empty) then
         let%modify trace := snoc ImplLeakage__Enq in
         let%write a      := in__a in
         let%write b      := in__b in
         let%write c      := 0%bv in
         let%write p      := 0%bv in
         let%write st     := State__Busy in
         pass
    }}.

  Definition deq :=
    {{ let%read st0 := st in
       let%read p0  := p  in
       if decide (st0 = State__Full) then
         let%modify trace := snoc ImplLeakage__Deq in
         let%write  st    := State__Empty          in
         ret (Valid p0)
       else
         ret Invalid
    }}.

  Definition shiftAndAdd :=
    {{ let%read a0 := a in
       let%read b0 := b in
       let%read c0 := c in
       let%read p0 := p in
       guard decide (a0 <> 0%bv) then
         let t :=
           if decide (truncate (z := 1) a0 = 1)%bv then
             zeroExtend (z := 8) b0
           else
             0%bv
         in
         let%write p := (p0 + (t ≪ zeroExtend (z := 8) c0))%bv in
         let%write a := (a0 ≫ 1)%bv in
         let%write c := (c0 + 1)%bv in
         pass
    }}.

  Definition rule :=
    {{ let%read st0 := st in
       let%read a0  := a  in
       guard decide (st0 = State__Busy) then
         let%modify trace := snoc ImplLeakage__Rule in
         if decide (a0 = 0%bv) then
           let%write st := State__Full in
           pass
         else
           shiftAndAdd
    }}.

  Instance circuit : Circuit :=
    {| circuitInit := mk
    ; circuitResult m := match m with Enq _ _ => unit | Deq => Maybe (Bit 8) | Rule => unit end
    ; circuitCall m := match m with Enq a b => enq a b | Deq => deq | Rule => rule end
    ; circuitTrace := trace
    |}.
End Multiplier.

Module MultiplierSpec.
  Record t :=
    { st : state
    ; a : Bit 4
    ; trace : list implLeakage
    }.

  Definition mk := {| st := State__Empty; a := 0%bv; trace := [] |}.

  Definition enq in__a :=
    {{ let%read st0 := st in
       guard decide (st0 = State__Empty) then
         let%modify trace := snoc ImplLeakage__Enq in
         let%write a := in__a in
         let%write st := State__Busy in
         pass
    }}.

  Definition deq :=
    {{ let%read st0 := st in
       guard decide (st0 = State__Full) then
         let%modify trace := snoc ImplLeakage__Deq in
         let%write st := State__Empty in
         pass
    }}.

  Definition shift :=
    {{ let%read a0 := a in
       guard decide (a0 <> 0%bv) then
         let%write a := (a0 ≫ 1)%bv in
         pass
    }}.

  Definition rule :=
    {{ let%read st0 := st in
       let%read a0 := a in
       guard decide (st0 = State__Busy) then
         let%modify trace := snoc ImplLeakage__Rule in
         if decide (a0 = 0%bv) then
           let%write st := State__Full in
           pass
         else
           shift
    }}.

  Instance circuit : Circuit :=
    {| circuitInit := mk
    ; circuitResult m :=
        match m with
        | SpecLeakage__Enq _  => unit
        | SpecLeakage__Deq => unit
        | SpecLeakage__Rule => unit
        end
    ; circuitCall m :=
        match m with
        | SpecLeakage__Enq a => enq a
        | SpecLeakage__Deq => deq
        | SpecLeakage__Rule => rule
        end
    ; circuitTrace := trace
    |}.
End MultiplierSpec.

Definition policy1 m :=
  match m with
  | Enq a b => SpecLeakage__Enq a
  | Deq => SpecLeakage__Deq
  | Rule => SpecLeakage__Rule
  end.

Definition policy := map policy1.

Definition inv (s1 : Multiplier.t) (s2 : MultiplierSpec.t) :=
  s1.(Multiplier.st) = s2.(MultiplierSpec.st) /\
    s1.(Multiplier.a) = s2.(MultiplierSpec.a) /\
    s1.(Multiplier.trace) = s2.(MultiplierSpec.trace).

Local Ltac t0 :=
  match goal with
  | m : method |- _ => destruct m
  | |- context [ decide _ ] => case_decide
  | |- _ /\ _ => split
  | |- constantTime _ _ => eapply simulationConstantTime
  end.

Local Ltac t1 :=
  unfold bind, fmap, modify, get,
    runAction2, runAction, circuitStep,
    Multiplier.enq, MultiplierSpec.enq,
    Multiplier.deq, MultiplierSpec.deq,
    Multiplier.rule, MultiplierSpec.rule,
    Multiplier.shiftAndAdd, MultiplierSpec.shift,
    runCircuit, simulates, inv in *.

Local Ltac t2 := solve [ equality | eauto 8 ].
Local Ltac t3 := simplify; t1; repeat (simplify; t1; try t0; try t2).
Local Ltac t := try t2; t3; t2.

Theorem simulatesOk : Multiplier.circuit ∼ MultiplierSpec.circuit : policy1; inv.
Proof.
  t.
Qed.

Local Hint Resolve simulatesOk : core.

Theorem constantTimeOk : constantTime Multiplier.circuit policy.
Proof.
  t.
Qed.
