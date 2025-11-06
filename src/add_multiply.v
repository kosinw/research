From research Require Import base.
From stdpp Require Import fin finite.
From research Require Import bit circuit multiplier fifo regfile.

Inductive Instr :=
| Add (rd rs1 rs2 : Bit 3)
| Addi (rd rs1 : Bit 3) (imm : Bit 8)
| Muli (rd : Bit 3) (imm : Bit 8) (rs2 : Bit 3)
| Nop.

Instance defaultInstr : Default Instr := Nop.

Inductive Method :=
| DeqIReq
| EnqIResp (resp : Instr)
| Rule.

Inductive State :=
| State__Fetch
| State__Decode
| State__Execute.

Inductive ImplLeakage :=
| Impl__Pc (l : Bit 32)
| Impl__Add
| Impl__Nop
| Impl__Mul (a : Bit 8).

Inductive SpecInstr :=
| SAdd
| SAddi
| SMul (imm : Bit 8)
| SNop.

Instance defaultSpecInstr : Default SpecInstr := SNop.

Inductive SpecLeakage :=
| Spec__DeqIReq
| Spec__EnqIResp (resp : SpecInstr)
| Spec__Rule.

Instance eqDecisionState : EqDecision State.
Proof.
  solve_decision.
Defined.

Inductive DInstr :=
| DAdd (rd : Bit 3) (v1 v2 : Bit 8)
| DMul (rd : Bit 3) (v1 v2 : Bit 8)
| DNop.

Instance defaultDInstr : Default DInstr := DNop.

Record AddMultiply :=
  { addMultiplyM        : Multiplier
  ; addMultiplyRf       : RegFile 8 3
  ; addMultiplyPc       : Bit 32
  ; addMultiplyFromImem : Fifo Instr
  ; addMultiplyToImem   : Fifo (Bit 32)
  ; addMultiplyDInstr   : Fifo DInstr
  ; addMultiplySt       : State
  ; addMultiplyTrace    : list ImplLeakage
  }.

Definition mkAddMultiply :=
  {|
    addMultiplyM         := mkMultiplier;
    addMultiplyRf        := mkRegFile;
    addMultiplyPc        := δ;
    addMultiplyFromImem  := mkFifo;
    addMultiplyToImem    := mkFifo;
    addMultiplyDInstr    := mkFifo;
    addMultiplySt        := State__Fetch;
    addMultiplyTrace     := δ
  |}.

Definition addMultiplyFetching st :=
  bool_decide (st.(addMultiplySt) = State__Fetch).

Definition addMultiplyDecoding st :=
  bool_decide (st.(addMultiplySt) = State__Decode).

Definition addMultiplyExecuting st :=
  bool_decide (st.(addMultiplySt) = State__Execute).

Definition addMultiplyGetIReq st := fifoFirst st.(addMultiplyToImem).

Definition addMultiplyDeqIReq :=
  {{ let%call _ := fifoDeq on addMultiplyToImem in
     pass
  }}.

Definition addMultiplyEnqIResp instr :=
  {{ let%call _ := fifoEnq instr on addMultiplyFromImem in
     pass
  }}.

Definition addMultiplyFetch :=
  guard
    {{ addMultiplyFetching }}
    {{ let%read pc := addMultiplyPc in
       let%call _ := fifoEnq pc on addMultiplyToImem in
       let%write _ := State__Decode on addMultiplySt in
       pass
    }}.

Definition addMultiplyDecode :=
  guard
    {{ addMultiplyDecoding }}
    {{ let%read rf       := addMultiplyRf in
       let%read instr    := fifoFirst ∘ addMultiplyFromImem in
       let%call _        := fifoDeq on addMultiplyFromImem in
       match instr with
       | Nop =>
           let%call  _ := fifoEnq DNop on addMultiplyDInstr in
           let%write _ := State__Execute on addMultiplySt in
           pass
       | Add rd rs1 rs2 =>
           let v1 := regFileSub rs1 rf in
           let v2 := regFileSub rs2 rf in
           let%call _ := fifoEnq (DAdd rd v1 v2) on addMultiplyDInstr in
           let%write _ := State__Execute on addMultiplySt in
           pass
       | Muli rd imm rs2 =>
           let v1 := imm in
           let v2 := regFileSub rs2 rf in
           let%call _ := fifoEnq (DMul rd v1 v2) on addMultiplyDInstr in
           let%write _ := State__Execute on addMultiplySt in
           pass
       | Addi rd rs1 imm =>
           let v1 := regFileSub rs1 rf in
           let%call _ := fifoEnq (DAdd rd v1 imm) on addMultiplyDInstr in
           let%write _ := State__Execute on addMultiplySt in
           pass
       end
    }}.

Definition addMultiplyExecuteAdd rd v1 v2 :=
  {{ let%read pc := addMultiplyPc in
     let%call _ := fifoDeq on addMultiplyDInstr in
     let%call _ := regFileUpd rd (v1 + v2)%bv on addMultiplyRf in
     let%write _ := State__Fetch on addMultiplySt in
     let%modify _ := cons (Impl__Pc pc) on addMultiplyTrace in
     let%modify _ := cons Impl__Add on addMultiplyTrace in
     let%modify _ := fun pc => (pc `+Z` 4)%bv on addMultiplyPc in
     pass
  }}.

Definition addMultiplyExecuteNop :=
  {{ let%read pc := addMultiplyPc in
     let%call _ := fifoDeq on addMultiplyDInstr in
     let%write _ := State__Fetch on addMultiplySt in
     let%modify _ := cons (Impl__Pc pc) on addMultiplyTrace in
     let%modify _ := cons Impl__Nop on addMultiplyTrace in
     let%modify _ := fun pc => (pc `+Z` 4)%bv on addMultiplyPc in
     pass
  }}.

Definition addMultiplyExecuteMul rd v1 v2 :=
  {{ let%read pc := addMultiplyPc in
     let%read st := multiplierSt ∘ addMultiplyM in
     match st with
     | State__Empty =>
         let%call _ := multiplierEnq v1 v2 on addMultiplyM in
         pass
     | State__Busy =>
         let%call _ := multiplierRule on addMultiplyM in
         pass
     | State__Full =>
         let%read v := (multiplierFirst ∘ addMultiplyM) in
         let%call _ := multiplierDeq on addMultiplyM in
         let%call _ := fifoDeq on addMultiplyDInstr in
         let%call _ := regFileUpd rd (truncate v) on addMultiplyRf in
         let%write _ := State__Fetch on addMultiplySt in
         let%modify _ := cons (Impl__Pc pc) on addMultiplyTrace in
         let%modify _ := cons (Impl__Mul v1) on addMultiplyTrace in
         let%modify _ := fun pc => (pc `+Z` 4)%bv on addMultiplyPc in
         pass
     end
  }}.

Definition addMultiplyExecute :=
  guard
    {{ addMultiplyExecuting }}
    {{ let%read instr := fifoFirst ∘ addMultiplyDInstr in
       match instr with
       | DAdd rd v1 v2 => addMultiplyExecuteAdd rd v1 v2
       | DMul rd v1 v2 => addMultiplyExecuteMul rd v1 v2
       | DNop => addMultiplyExecuteNop
       end
    }}.

Definition addMultiplyRule :=
  {{ let%read st := addMultiplySt in
     match st with
     | State__Fetch => addMultiplyFetch
     | State__Decode => addMultiplyDecode
     | State__Execute => addMultiplyExecute
     end
  }}.

Instance addMultiplyCircuit : Circuit :=
  {|
    mkCircuit := mkAddMultiply;
    circuitCall m :=
      match m with
      | DeqIReq => addMultiplyDeqIReq
      | EnqIResp resp => addMultiplyEnqIResp resp
      | Rule => addMultiplyRule
      end;
    circuitTrace := addMultiplyTrace
  |}.

Record AddMultiplySpec :=
  { addMultiplySpecM        : MultiplierSpec
  ; addMultiplySpecPc       : Bit 32
  ; addMultiplySpecFromImem : Fifo SpecInstr
  ; addMultiplySpecToImem   : Fifo (Bit 32)
  ; addMultiplySpecDInstr   : Fifo SpecInstr
  ; addMultiplySpecSt       : State
  ; addMultiplySpecTrace    : list ImplLeakage
  }.

Definition mkAddMultiplySpec :=
  {|
    addMultiplySpecM         := mkMultiplierSpec;
    addMultiplySpecPc        := δ;
    addMultiplySpecFromImem  := mkFifo;
    addMultiplySpecToImem    := mkFifo;
    addMultiplySpecDInstr    := mkFifo;
    addMultiplySpecSt        := State__Fetch;
    addMultiplySpecTrace     := δ
  |}.

Definition addMultiplySpecFetching st :=
  bool_decide (st.(addMultiplySpecSt) = State__Fetch).

Definition addMultiplySpecDecoding st :=
  bool_decide (st.(addMultiplySpecSt) = State__Decode).

Definition addMultiplySpecExecuting st :=
  bool_decide (st.(addMultiplySpecSt) = State__Execute).

Definition addMultiplySpecDeqIReq :=
  {{ let%call _ := fifoDeq on addMultiplySpecToImem in
     pass
  }}.

Definition addMultiplySpecEnqIResp instr :=
  {{ let%call _ := fifoEnq instr on addMultiplySpecFromImem in
     pass
  }}.

Definition addMultiplySpecFetch :=
  guard
    {{ addMultiplySpecFetching }}
    {{ let%read pc := addMultiplySpecPc in
       let%write _ := State__Decode on addMultiplySpecSt in
       let%call _ := fifoEnq pc on addMultiplySpecToImem in
       pass
    }}.

Definition addMultiplySpecDecode :=
  guard
    {{ addMultiplySpecDecoding }}
    {{ let%read instr    := fifoFirst ∘ addMultiplySpecFromImem in
       let%call _        := fifoDeq on addMultiplySpecFromImem in
       let%call _        := fifoEnq instr on addMultiplySpecDInstr in
       let%write _       := State__Execute on addMultiplySpecSt in
       pass
    }}.

Definition addMultiplySpecExecuteAdd :=
  {{ let%read pc := addMultiplySpecPc in
     let%call _ := fifoDeq on addMultiplySpecDInstr in
     let%write _ := State__Fetch on addMultiplySpecSt in
     let%modify _ := cons (Impl__Pc pc) on addMultiplySpecTrace in
     let%modify _ := cons Impl__Add on addMultiplySpecTrace in
     let%modify _ := fun pc => (pc `+Z` 4)%bv on addMultiplySpecPc in
     pass
  }}.

Definition addMultiplySpecExecuteNop :=
  {{ let%read pc := addMultiplySpecPc in
     let%call _ := fifoDeq on addMultiplySpecDInstr in
     let%write _ := State__Fetch on addMultiplySpecSt in
     let%modify _ := cons (Impl__Pc pc) on addMultiplySpecTrace in
     let%modify _ := cons Impl__Nop on addMultiplySpecTrace in
     let%modify _ := fun pc => (pc `+Z` 4)%bv on addMultiplySpecPc in
     pass
  }}.

Definition addMultiplySpecExecuteMul v1 :=
  {{ let%read pc := addMultiplySpecPc in
     let%read st := multiplierSpecSt ∘ addMultiplySpecM in
     match st with
     | State__Empty =>
         let%call _ := multiplierSpecEnq v1 on addMultiplySpecM in
         pass
     | State__Busy =>
         let%call _ := multiplierSpecRule on addMultiplySpecM in
         pass
     | State__Full =>
         let%call _ := multiplierSpecDeq on addMultiplySpecM in
         let%call _ := fifoDeq on addMultiplySpecDInstr in
         let%write _ := State__Fetch on addMultiplySpecSt in
         let%modify _ := cons (Impl__Pc pc) on addMultiplySpecTrace in
         let%modify _ := cons (Impl__Mul v1) on addMultiplySpecTrace in
         let%modify _ := fun pc => (pc `+Z` 4)%bv on addMultiplySpecPc in
         pass
     end
  }}.

Definition addMultiplySpecExecute :=
  guard
    {{ addMultiplySpecExecuting }}
    {{ let%read instr := fifoFirst ∘ addMultiplySpecDInstr in
       match instr with
       | SAddi | SAdd => addMultiplySpecExecuteAdd
       | SMul v1 => addMultiplySpecExecuteMul v1
       | SNop => addMultiplySpecExecuteNop
       end
    }}.

Definition addMultiplySpecRule :=
  {{ let%read st := addMultiplySpecSt in
     match st with
     | State__Fetch => addMultiplySpecFetch
     | State__Decode => addMultiplySpecDecode
     | State__Execute => addMultiplySpecExecute
     end
  }}.

Instance addMultiplySpecCircuit : Circuit :=
  {|
    mkCircuit := mkAddMultiplySpec;
    circuitCall m :=
      match m with
      | Spec__DeqIReq => addMultiplySpecDeqIReq
      | Spec__EnqIResp resp => addMultiplySpecEnqIResp resp
      | Spec__Rule => addMultiplySpecRule
      end;
    circuitTrace := addMultiplySpecTrace
  |}.

(* Names of RISC-V-like registers *)
Definition x0 := 3`0%bv.
Definition x1 := 3`1%bv.
Definition x2 := 3`2%bv.
Definition x3 := 3`3%bv.
Definition x4 := 3`4%bv.
Definition x5 := 3`5%bv.
Definition x6 := 3`6%bv.
Definition x7 := 3`7%bv.

(* Notation for RISC-V-like instructions *)
Declare Scope asm_scope.
Delimit Scope asm_scope with asm.

Notation "'addi' rd , rs1 , imm" := (Addi rd rs1 imm)%bv (at level 0) : asm_scope.
Notation "'li' rd , imm" := (Addi rd 3`0 imm)%bv (at level 0) : asm_scope.
Notation "'mv' rd , rs" := (Addi rd rs 0)%bv (at level 0) : asm_scope.
Notation "'add' rd , rs1 , rs2" := (Add rd rs1 rs2)%bv (at level 0) : asm_scope.
Notation "'muli' rd , imm , rs2" := (Muli rd imm rs2)%bv (at level 0) : asm_scope.
Notation "'nop'" := Nop (at level 0) : asm_scope.

(* Execute a single instruction until completion *)
Definition executeOneInstr (fuel : nat) (instr : Instr) (st : AddMultiply) : AddMultiply :=
  (* Fetch stage: send PC to instruction memory *)
  let st1 := circuitSteps addMultiplyCircuit [Rule; DeqIReq; EnqIResp instr] st in
  (* Decode stage *)
  let st2 := circuitStep addMultiplyCircuit Rule st1 in
  (* Execute stage - may take multiple cycles *)
  let fix executeUntilFetch (fuel : nat) (st : AddMultiply) : AddMultiply :=
    match fuel with
    | 0 => st
    | S fuel' =>
        let st' := circuitStep addMultiplyCircuit Rule st in
        if decide (st'.(addMultiplySt) = State__Fetch) then
          st'
        else
          executeUntilFetch fuel' st'
    end
  in
  executeUntilFetch fuel st2.

(* Execute instructions with fuel *)
Fixpoint execute (instrs : list Instr) (st : AddMultiply) : AddMultiply :=
  match instrs with
  | [] => st
  | instr :: instrs' =>
      let st' := executeOneInstr 100 instr st in
      execute instrs' st'
  end.

(* Extract the specification leakage trace from the series of Methods. *)
Definition policy__dinstr (dinstr : DInstr) : SpecInstr :=
  match dinstr with
  | DNop => SNop
  | DAdd _ _ _ => SAdd
  | DMul _ imm _ => SMul imm
  end.

Definition policy__instr (instr : Instr) : SpecInstr :=
  match instr with
  | Nop => SNop
  | Add rd rs1 rs2 => SAdd
  | Addi rd rs1 imm => SAdd
  | Muli rd imm rs2 => SMul imm
  end.

Definition policy1 (m : Method) : SpecLeakage :=
  match m with
  | Rule => Spec__Rule
  | DeqIReq => Spec__DeqIReq
  | EnqIResp instr => Spec__EnqIResp (policy__instr instr)
  end.

Definition policy := map policy1.

Definition instrRel instr sinstr :=
  Eval cbv delta [ policy__instr ] in
    sinstr = policy__instr instr.

Definition dinstrRel dinstr sinstr :=
  Eval cbv delta [ policy__dinstr ] in
    sinstr = policy__dinstr dinstr.

Definition addMultiplyRel st1 st2 :=
  rel st1.(addMultiplyM) st2.(addMultiplySpecM)
  /\ st1.(addMultiplyPc) = st2.(addMultiplySpecPc)
  /\ st1.(addMultiplySt) = st2.(addMultiplySpecSt)
  /\ st1.(addMultiplyTrace) = st2.(addMultiplySpecTrace)
  /\ st1.(addMultiplyToImem) = st2.(addMultiplySpecToImem)
  /\ fifoLift instrRel st1.(addMultiplyFromImem) st2.(addMultiplySpecFromImem)
  /\ fifoLift dinstrRel st1.(addMultiplyDInstr) st2.(addMultiplySpecDInstr).

Local Hint Unfold fifoDeq fifoFirst fifoEnq fifoNotEmpty fifoNotFull : core.
Local Hint Unfold addMultiplyRel : core.
Local Hint Unfold circuitStep nextState set policy__instr : core.
Local Hint Unfold addMultiplyFetching addMultiplySpecFetching : core.
Local Hint Unfold addMultiplyExecuting addMultiplySpecExecuting : core.
Local Hint Unfold addMultiplyExecuteAdd addMultiplySpecExecuteAdd : core.
Local Hint Unfold addMultiplyExecuteNop addMultiplySpecExecuteNop : core.
Local Hint Unfold addMultiplyExecuteMul addMultiplySpecExecuteMul : core.

Local Ltac t0 :=
  match goal with
  | H0 : fifoLift ?R ?A1 ?A2,
      H1 : fifoContents ?A1 = None,
        H2 : fifoContents ?A2 = None -> False
    |- _ =>
      assert (~ fifoLift R A1 A2) by eauto;
      clear H1 H2
  | H0 : fifoLift ?R ?A1 ?A2,
      H1 : fifoContents ?A1 = None -> False,
        H2 : fifoContents ?A2 = None
    |- _ =>
      assert (~ fifoLift R A1 A2) by eauto;
      clear H1 H2
  | m : Method |- _ => destruct m
  | i : Instr |- _ => destruct i
  | |- context [ decide _ ] => case_decide
  | |- context [ bool_decide _ ] => case_bool_decide
  | H : _ /\ _ |- _ => propositional
  | |- _ /\ _ => propositional
  | _ => try solve [ equality | eauto 8 ]; progress simplify
  end.

Local Ltac t := repeat t0.

Lemma deqOk : addMultiplyDeqIReq ⪯ addMultiplySpecDeqIReq : addMultiplyRel.
Proof.
  cbv [ simulates addMultiplyDeqIReq addMultiplySpecDeqIReq ]; t.
Qed.

Lemma enqOk : forall resp,
    addMultiplyEnqIResp resp ⪯ addMultiplySpecEnqIResp (policy__instr resp) : addMultiplyRel.
Proof.
  cbv [ simulates addMultiplyEnqIResp addMultiplySpecEnqIResp ]; t.
Qed.

Lemma fetchOk : addMultiplyFetch ⪯ addMultiplySpecFetch : addMultiplyRel.
Proof.
  cbv [ simulates addMultiplyFetch addMultiplySpecFetch ]; t.
Qed.

Local Hint Resolve fetchOk : core.

Lemma ruleOk : addMultiplyRule ⪯ addMultiplySpecRule : addMultiplyRel. Admitted.

Local Hint Resolve ruleOk deqOk enqOk : core.

Lemma simOk : addMultiplyCircuit ∼ addMultiplySpecCircuit : policy1 ; addMultiplyRel.
Proof.
  cbv [ circuitSimulates ]; t.
Qed.

Local Hint Resolve simOk : core.

Theorem constantTimeOk : constantTime addMultiplyCircuit policy.
  apply circuitConstantTime with
    (c2 := addMultiplySpecCircuit)
    (R := addMultiplyRel);
    t.
  - cbv [ rel ]; t.
  - cbv [ fifoLift instrRel ]; t.
  - cbv [ fifoLift dinstrRel ]; t.
Qed.
