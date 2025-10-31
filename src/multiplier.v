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

Record Multiplier :=
  { multiplierA : Bit 4
  ; multiplierB : Bit 4
  ; multiplierC : Bit 2
  ; multiplierP : Bit 8
  ; multiplierSt : state
  ; multiplierTrace : list implLeakage
  }.

Definition mkMultiplier :=
  {|
    multiplierA := 0%bv;
    multiplierB := 0%bv;
    multiplierC := 0%bv;
    multiplierP := 0%bv;
    multiplierSt := State__Empty;
    multiplierTrace := []
  |}.

Definition multiplierEnq in__a in__b :=
  {{ let%read st := multiplierSt in
     when decide (st = State__Empty) then
       let%modify multiplierTrace := snoc ImplLeakage__Enq in
       let%write multiplierA      := in__a in
       let%write multiplierB      := in__b in
       let%write multiplierC      := 0%bv in
       let%write multiplierP      := 0%bv in
       let%write multiplierSt     := State__Busy in
       pass
  }}.

Definition multiplierDeq :=
  {{ let%read st := multiplierSt in
     let%read p  := multiplierP  in
     if decide (st = State__Full) then
       let%modify multiplierTrace := snoc ImplLeakage__Deq in
       let%write  multiplierSt    := State__Empty          in
       ret (Valid p)
     else
       ret Invalid
  }}.

Definition multiplierShiftAndAdd :=
  {{ let%read a := multiplierA in
     let%read b := multiplierB in
     let%read c := multiplierC in
     let%read p := multiplierP in
     when decide (a <> 0%bv) then
       let t :=
         if decide (truncate1 a = 1)%bv then
           zeroExtend (z := 8) b
         else
           0%bv
       in
       let%write multiplierP := (p + (t ≪ zeroExtend c))%bv in
       let%write multiplierA := (a ≫ 1)%bv in
       let%write multiplierC := (c + 1)%bv in
       pass
  }}.

Definition multiplierRule :=
  {{ let%read st := multiplierSt in
     let%read a  := multiplierA  in
     when decide (st = State__Busy) then
       let%modify multiplierTrace := snoc ImplLeakage__Rule in
       if decide (a = 0%bv) then
         let%write multiplierSt := State__Full in
         pass
       else
         multiplierShiftAndAdd
  }}.

Instance multiplierCircuit : Circuit :=
  {|
    circuitInit := mkMultiplier;
    circuitResult m :=
      match m with
      | Enq _ _ => unit
      | Deq => Maybe (Bit 8)
      | Rule => unit
      end;
    circuitCall m :=
      match m with
      | Enq a b => multiplierEnq a b
      | Deq => multiplierDeq
      | Rule => multiplierRule
      end;
    circuitTrace := multiplierTrace
  |}.

Record MultiplierSpec :=
  { multiplierSpecSt : state
  ; multiplierSpecA : Bit 4
  ; multiplierSpecTrace : list implLeakage
  }.

Definition mkMultiplierSpec :=
  {|
    multiplierSpecSt := State__Empty;
    multiplierSpecA := 0%bv;
    multiplierSpecTrace := []
  |}.

Definition multiplierSpecEnq in__a :=
  {{ let%read st := multiplierSpecSt in
     when decide (st = State__Empty) then
       let%modify multiplierSpecTrace := snoc ImplLeakage__Enq in
       let%write multiplierSpecA := in__a in
       let%write multiplierSpecSt := State__Busy in
       pass
  }}.

Definition multiplierSpecDeq :=
  {{ let%read st := multiplierSpecSt in
     when decide (st = State__Full) then
       let%modify multiplierSpecTrace := snoc ImplLeakage__Deq in
       let%write multiplierSpecSt := State__Empty in
       pass
  }}.

Definition multiplierSpecShift :=
  {{ let%read a := multiplierSpecA in
     when decide (a <> 0%bv) then
       let%write multiplierSpecA := (a ≫ 1)%bv in
       pass
  }}.

Definition multiplierSpecRule :=
  {{ let%read st := multiplierSpecSt in
     let%read a := multiplierSpecA in
     when decide (st = State__Busy) then
       let%modify multiplierSpecTrace := snoc ImplLeakage__Rule in
       if decide (a = 0%bv) then
         let%write multiplierSpecSt := State__Full in
         pass
       else
         multiplierSpecShift
  }}.

Instance multiplierSpecCircuit : Circuit :=
  {|
    circuitInit := mkMultiplierSpec;
    circuitResult m := unit;
    circuitCall m :=
      match m with
      | SpecLeakage__Enq a => multiplierSpecEnq a
      | SpecLeakage__Deq => multiplierSpecDeq
      | SpecLeakage__Rule => multiplierSpecRule
      end;
    circuitTrace := multiplierSpecTrace
  |}.

Definition policy1 m :=
  match m with
  | Enq a b => SpecLeakage__Enq a
  | Deq => SpecLeakage__Deq
  | Rule => SpecLeakage__Rule
  end.

Definition policy := map policy1.

Definition inv (s1 : Multiplier) (s2 : MultiplierSpec) :=
  s1.(multiplierSt) = s2.(multiplierSpecSt) /\
    s1.(multiplierA) = s2.(multiplierSpecA) /\
    s1.(multiplierTrace) = s2.(multiplierSpecTrace).

Local Ltac t0 :=
  match goal with
  | m : method |- _ => destruct m
  | |- context [ decide _ ] => case_decide
  | _ => progress simplify
  end.

Local Hint Unfold
  multiplierEnq multiplierSpecEnq
  multiplierDeq multiplierSpecDeq
  multiplierRule multiplierSpecRule
  multiplierShiftAndAdd multiplierSpecShift
  circuitStep inv : core.

Local Ltac t := repeat t0; solve [ equality | eauto 8 ].

Theorem simulatesOk : multiplierCircuit ∼ multiplierSpecCircuit : policy1; inv.
Proof.
  cbv [ simulates ] in *.
  t.
Qed.

Local Hint Resolve simulatesOk : core.

Theorem constantTimeOk : constantTime multiplierCircuit policy.
Proof.
  apply simulationConstantTime with (R := inv) (c2 := multiplierSpecCircuit); t.
Qed.
