From research Require Import base.
From stdpp Require Import fin finite.
From research Require Import bit circuit multiplier fifo regfile.

Inductive Instr :=
| Add (rd rs1 rs2 : Bit 5)
| Addi (rd rs1 : Bit 5) (imm : Bit 8)
| Mul (rd rs1 rs2 : Bit 5)
| Nop
| Unknown.

Instance defaultInstr : Default Instr := Nop.

Inductive method :=
| DeqIReq
| EnqIResp (resp : Instr)
| Rule.

Inductive state :=
| State__Fetch
| State__Decode
| State__Execute.

Inductive implLeakage :=
| Impl__Pc (l : Bit 32)
| Impl__Add
| Impl__Nop
| Impl__Mul (a : Bit 8).

Instance state__EqDecision : EqDecision state.
Proof.
  solve_decision.
Defined.

Inductive DInstr :=
| DAdd (rd : Bit 5) (v1 v2 : Bit 8)
| DMul (rd : Bit 5) (v1 v2 : Bit 8)
| DNop.

Instance defaultDInstr : Default DInstr := DNop.

Record AddMultiply :=
  { addMultiplyM        : Multiplier
  ; addMultiplyRf       : RegFile 8 5
  ; addMultiplyPc       : Bit 32
  ; addMultiplyFromImem : Fifo Instr
  ; addMultiplyToImem   : Fifo (Bit 32)
  ; addMultiplyDInstr   : Fifo DInstr
  ; addMultiplySt       : state
  ; addMultiplyTrace    : list implLeakage
  }.

Definition mkAddMultiply :=
  {|
    addMultiplyM         := mkMultiplier;
    addMultiplyRf        := mkRegFile;
    addMultiplyPc        := 0%bv;
    addMultiplyFromImem  := mkFifo;
    addMultiplyToImem    := mkFifo;
    addMultiplyDInstr    := mkFifo;
    addMultiplySt        := State__Fetch;
    addMultiplyTrace     := []
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
    {{ let%read d2e      := addMultiplyDInstr in
       let%read rf       := addMultiplyRf in
       let%read instr    := fifoFirst ∘ addMultiplyFromImem in
       let%call _        := fifoDeq on addMultiplyFromImem in
       match instr with
       | Nop
       | Unknown =>
           let%call  _ := fifoEnq DNop on addMultiplyDInstr in
           let%write _ := State__Execute on addMultiplySt in
           pass
       | Add rd rs1 rs2 =>
           let v1 := regFileSub rs1 rf in
           let v2 := regFileSub rs2 rf in
           let%call _ := fifoEnq (DAdd rd v1 v2) on addMultiplyDInstr in
           let%write _ := State__Execute on addMultiplySt in
           pass
       | Mul rd rs1 rs2 =>
           let v1 := regFileSub rs1 rf in
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

Section example.
  Definition x0 := 5`0%bv.
  Definition x1 := 5`1%bv.
  Definition x2 := 5`2%bv.
  Definition x3 := 5`3%bv.
  Definition x4 := 5`4%bv.
  Definition x5 := 5`5%bv.
  Definition x6 := 5`6%bv.
  Definition x7 := 5`7%bv.
  Definition x8 := 5`8%bv.

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
          if bool_decide (st'.(addMultiplySt) = State__Fetch) then st'
          else executeUntilFetch fuel' st'
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

  (* Notation for RISC-V-like instructions *)
  Declare Scope asm_scope.
  Delimit Scope asm_scope with asm.

  Notation "'li' rd , imm" := (Addi rd 5`0 imm)%bv (at level 0) : asm_scope.
  Notation "'mv' rd , rs" := (Addi rd rs 0)%bv (at level 0) : asm_scope.
  Notation "'addi' rd , rs1 , imm" := (Addi rd rs1 imm)%bv (at level 0) : asm_scope.
  Notation "'add' rd , rs1 , rs2" := (Add rd rs1 rs2)%bv (at level 0) : asm_scope.
  Notation "'mul' rd , rs1 , rs2" := (Mul rd rs1 rs2)%bv (at level 0) : asm_scope.
  Notation "'nop'" := Nop (at level 0) : asm_scope.
  Notation "'unk'" := Unknown (at level 0) : asm_scope.

  Local Open Scope asm_scope.

  Example ex1 := [
      li x1, 127;
      li x2, 1;
      mul x3, x1, x2;
      nop;
      nop;
      nop;
      add x4, x3, x3
    ].

  Eval vm_compute in (execute ex1 mkAddMultiply).

  Example ex2 := [
      li x1, 15;
      li x2, 30;
      add x8, x1, x2;
      mv x3, x8
    ].

  Eval vm_compute in (execute ex2 mkAddMultiply).
End example.
