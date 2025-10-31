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

Definition multiplierEmpty st := bool_decide (st.(multiplierSt) = State__Empty).
Definition multiplierBusy st := bool_decide (st.(multiplierSt) = State__Busy).
Definition multiplierFull st := bool_decide (st.(multiplierSt) = State__Full).

Definition multiplierEnq x1 x2 : Action unit :=
  guard
    {{ multiplierEmpty }}
    {{ let%modify _ := snoc ImplLeakage__Enq on multiplierTrace in
       let%write  _ := x1 on multiplierA in
       let%write  _ := x2 on multiplierB in
       let%write  _ := 0%bv on multiplierC in
       let%write  _ := 0%bv on multiplierP in
       let%write  _ := State__Busy on multiplierSt in
       pass
    }}.

Definition multiplierDeq : Action (Bit 8) :=
  guard
    {{ multiplierFull }}
    {{ let%read p  := multiplierP  in
       let%modify _ := snoc ImplLeakage__Deq on multiplierTrace in
       let%write _ := State__Empty on multiplierSt in
       ret p
    }}.

Definition multiplierShiftAndAdd : Action unit :=
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
       let%write _ := (p + (t ≪ zeroExtend c))%bv on multiplierP in
       let%write _ := (a ≫ 1)%bv on multiplierA in
       let%write _ := (c + 1)%bv on multiplierC in
       pass
  }}.

Definition multiplierRule : Action unit :=
  guard
    {{ multiplierBusy }}
    {{ let%read a := multiplierA in
       let%modify _ := snoc ImplLeakage__Rule on multiplierTrace in
       if decide (a = 0%bv) then
         let%write _ := State__Full on multiplierSt in
         pass
       else
         multiplierShiftAndAdd
    }}.

Instance multiplierCircuit : Circuit :=
  {|
    mkCircuit := mkMultiplier;
    circuitResult m :=
      match m with
      | Enq _ _ => unit
      | Deq => Bit 8
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

Definition multiplierSpecEmpty st := bool_decide (st.(multiplierSpecSt) = State__Empty).
Definition multiplierSpecBusy st := bool_decide (st.(multiplierSpecSt) = State__Busy).
Definition multiplierSpecFull st := bool_decide (st.(multiplierSpecSt) = State__Full).

Definition multiplierSpecEnq in__a :=
  guard
    {{ multiplierSpecEmpty }}
    {{ let%modify _ := snoc ImplLeakage__Enq on multiplierSpecTrace in
       let%write _ := in__a on multiplierSpecA in
       let%write _ := State__Busy on multiplierSpecSt in
       pass
    }}.

Definition multiplierSpecDeq :=
  guard
    {{ multiplierSpecFull }}
    {{ let%modify _ := snoc ImplLeakage__Deq on multiplierSpecTrace in
       let%write _ := State__Empty on multiplierSpecSt in
       pass
    }}.

Definition multiplierSpecShift :=
  {{ let%read a := multiplierSpecA in
     when decide (a <> 0%bv) then
       let%write _ := (a ≫ 1)%bv on multiplierSpecA in
       pass
  }}.

Definition multiplierSpecRule :=
  guard
    {{ multiplierSpecBusy }}
    {{ let%read a := multiplierSpecA in
       let%modify _ := snoc ImplLeakage__Rule on multiplierSpecTrace in
       if decide (a = 0%bv) then
         let%write _ := State__Full on multiplierSpecSt in
         pass
       else
         multiplierSpecShift
    }}.

Instance multiplierSpecCircuit : Circuit :=
  {|
    mkCircuit := mkMultiplierSpec;
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
  | |- context [ bool_decide _ ] => case_bool_decide
  | _ => progress simplify
  end.

Local Hint Unfold
  multiplierEnq multiplierSpecEnq
  multiplierDeq multiplierSpecDeq
  multiplierRule multiplierSpecRule
  multiplierShiftAndAdd multiplierSpecShift
  multiplierEmpty multiplierSpecEmpty
  multiplierBusy multiplierSpecBusy
  multiplierFull multiplierSpecFull
  circuitStep inv : core.

Local Ltac t := repeat t0; solve [ equality | eauto 8 ].

Theorem simulatesOk : multiplierCircuit ∼ multiplierSpecCircuit : policy1; inv.
Proof.
  cbv [ simulates ]; t.
Qed.

Local Hint Resolve simulatesOk : core.

Theorem constantTimeOk : constantTime multiplierCircuit policy.
Proof.
  apply simulationConstantTime with (R := inv) (c2 := multiplierSpecCircuit); t.
Qed.
