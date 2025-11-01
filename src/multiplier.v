From research Require Import base bit circuit.

Section WithContext.
  Inductive specLeakage :=
  | Spec__Enq (a : Bit 8)
  | Spec__Deq
  | Spec__Rule.

  Inductive implLeakage :=
  | Impl__Enq
  | Impl__Deq
  | Impl__Rule.

  Inductive method :=
  | Enq (a b : Bit 8)
  | Deq
  | Rule.

  Inductive state :=
  | State__Empty
  | State__Busy
  | State__Full.

  Instance state__EqDecision : EqDecision state. solve_decision. Defined.

  Record Multiplier :=
    { multiplierA     : Bit 8
    ; multiplierB     : Bit 8
    ; multiplierC     : Bit 3
    ; multiplierP     : Bit 16
    ; multiplierSt    : state
    ; multiplierTrace : list implLeakage
    }.

  Definition mkMultiplier :=
    {|
      multiplierA     := 0%bv;
      multiplierB     := 0%bv;
      multiplierC     := 0%bv;
      multiplierP     := 0%bv;
      multiplierSt    := State__Empty;
      multiplierTrace := []
    |}.

  Definition multiplierEmpty st :=
    bool_decide (st.(multiplierSt) = State__Empty).

  Definition multiplierBusy st :=
    bool_decide (st.(multiplierSt) = State__Busy).

  Definition multiplierFull st :=
    bool_decide (st.(multiplierSt) = State__Full).

  Definition multiplierEnq x1 x2 :=
    guard
      {{ multiplierEmpty }}
      {{ let%modify _ := cons Impl__Enq on multiplierTrace in
         let%write  _ := x1 on multiplierA in
         let%write  _ := x2 on multiplierB in
         let%write  _ := 0%bv on multiplierC in
         let%write  _ := 0%bv on multiplierP in
         let%write  _ := State__Busy on multiplierSt in
         pass
      }}.

  Definition multiplierFirst st := st.(multiplierP).

  Definition multiplierDeq :=
    guard
      {{ multiplierFull }}
      {{ let%read p := multiplierP  in
         let%modify _ := cons Impl__Deq on multiplierTrace in
         let%write _ := State__Empty on multiplierSt in
         pass
      }}.

  Definition multiplierShiftAndAdd : Action unit :=
    {{ let%read a := multiplierA in
       let%read b := multiplierB in
       let%read c := multiplierC in
       let%read p := multiplierP in
       when decide (a <> 0%bv) then
         let t :=
           if decide (truncate1 a = 1)%bv then
             zeroExtend b
           else
             (16`0x00)%bv
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
         let%modify _ := cons Impl__Rule on multiplierTrace in
         if decide (a = 0%bv) then
           let%write _ := State__Full on multiplierSt in
           pass
         else
           multiplierShiftAndAdd
      }}.

  Instance multiplierCircuit : Circuit :=
    {|
      mkCircuit := mkMultiplier;
      circuitCall m :=
        match m with
        | Enq a b => multiplierEnq a b
        | Deq => multiplierDeq
        | Rule => multiplierRule
        end;
      circuitTrace := multiplierTrace
    |}.

  Record MultiplierSpec :=
    { multiplierSpecSt    : state
    ; multiplierSpecA     : Bit 8
    ; multiplierSpecTrace : list implLeakage
    }.

  Definition mkMultiplierSpec :=
    {|
      multiplierSpecSt    := State__Empty;
      multiplierSpecA     := 0%bv;
      multiplierSpecTrace := []
    |}.

  Definition multiplierSpecEmpty st :=
    bool_decide (st.(multiplierSpecSt) = State__Empty).

  Definition multiplierSpecBusy st :=
    bool_decide (st.(multiplierSpecSt) = State__Busy).

  Definition multiplierSpecFull st :=
    bool_decide (st.(multiplierSpecSt) = State__Full).

  Definition multiplierSpecEnq in__a :=
    guard
      {{ multiplierSpecEmpty }}
      {{ let%modify _ := cons Impl__Enq on multiplierSpecTrace in
         let%write _ := in__a on multiplierSpecA in
         let%write _ := State__Busy on multiplierSpecSt in
         pass
      }}.

  Definition multiplierSpecDeq :=
    guard
      {{ multiplierSpecFull }}
      {{ let%modify _ := cons Impl__Deq on multiplierSpecTrace in
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
         let%modify _ := cons Impl__Rule on multiplierSpecTrace in
         if decide (a = 0%bv) then
           let%write _ := State__Full on multiplierSpecSt in
           pass
         else
           multiplierSpecShift
      }}.

  Instance multiplierSpecCircuit : Circuit :=
    {|
      mkCircuit := mkMultiplierSpec;
      circuitCall m :=
        match m with
        | Spec__Enq a => multiplierSpecEnq a
        | Spec__Deq => multiplierSpecDeq
        | Spec__Rule => multiplierSpecRule
        end;
      circuitTrace := multiplierSpecTrace
    |}.

  Definition policy1 m :=
    match m with
    | Enq a b => Spec__Enq a
    | Deq => Spec__Deq
    | Rule => Spec__Rule
    end.

  Definition policy := map policy1.

  Definition rel (s1 : Multiplier) (s2 : MultiplierSpec) :=
    s1.(multiplierSt) = s2.(multiplierSpecSt) /\
      s1.(multiplierA) = s2.(multiplierSpecA) /\
      s1.(multiplierTrace) = s2.(multiplierSpecTrace).

  Local Hint Unfold
    multiplierShiftAndAdd multiplierSpecShift
    multiplierEmpty multiplierSpecEmpty
    multiplierBusy multiplierSpecBusy
    multiplierFull multiplierSpecFull : core.

  Local Hint Unfold rel circuitStep : core.

  Local Ltac t0 :=
    match goal with
    | m : method |- _ => destruct m
    | |- context [ decide _ ] => case_decide
    | |- context [ bool_decide _ ] => case_bool_decide
    | |- _ ≺ _ : _ => try eauto 8
    | _ => progress simplify
    end.

  Local Ltac t := repeat t0; solve [ equality | eauto 8 ].

  Lemma multiplierEnqOk : forall a b, multiplierEnq a b ≺ multiplierSpecEnq a : rel.
  Proof.
    cbv [ simulates multiplierEnq multiplierSpecEnq ]; t.
  Qed.

  Lemma multiplierDeqOk : multiplierDeq ≺ multiplierSpecDeq : rel.
  Proof.
    cbv [ simulates multiplierDeq multiplierSpecDeq ]; t.
  Qed.

  Lemma multiplierRuleOk : multiplierRule ≺ multiplierSpecRule : rel.
  Proof.
    cbv [ simulates multiplierRule multiplierSpecRule ]; t.
  Qed.

  Local Hint Resolve multiplierEnqOk multiplierDeqOk multiplierRuleOk : core.

  Theorem multiplierSimulatesOk : multiplierCircuit ∼ multiplierSpecCircuit : policy1; rel.
  Proof.
    cbv [ circuitSimulates ]; t.
  Qed.

  Local Hint Resolve multiplierSimulatesOk : core.

  Theorem multiplierConstantTime : constantTime multiplierCircuit policy.
  Proof.
    apply circuitConstantTime with (R := rel) (c2 := multiplierSpecCircuit); t.
  Qed.
End WithContext.
