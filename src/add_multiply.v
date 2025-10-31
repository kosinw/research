From stdpp Require Import fin finite.
From research Require Import base bit circuit multiplier fifo regfile.

Notation Maybe := @option.

Inductive Instr :=
| Add (rd rs1 rs2 : Bit 5)
| Addi (rd rs1 : Bit 5) (imm : Bit 4)
| Mul (rd rs1 rs2 : Bit 5)
| Nop
| Unknown.

Instance defaultInstr : Default Instr := Nop.

Inductive method :=
| GetIReq
| GetIResp (resp : Instr)
| Rule.

Inductive state :=
| State__Fetch
| State__Decode
| State__Execute.

Inductive implLeakage :=
| ImplLeak__Pc (l : Bit 32)
| ImplLeak__Add
| ImplLeak__Nop
| ImplLeak__Mul (a : Bit 4).

Instance state__EqDecision : EqDecision state.
Proof.
  solve_decision.
Defined.

Inductive DInstr :=
| DAdd (rd : Bit 5) (v1 v2 : Bit 4)
| DMul (rd : Bit 5) (v1 v2 : Bit 4)
| DNop.

Instance defaultDInstr : Default DInstr := DNop.

Record AddMultiply :=
  { addMultiplyM        : Multiplier
  ; addMultiplyRf       : RegFile 4 5
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

Definition addMultiplyGetIReq :=
  {{ let%call d := fifoFirst on addMultiplyToImem in
     let%call _ := fifoDeq on addMultiplyToImem in
     ret d
  }}.

Definition addMultiplyGetIResp instr :=
  {{ let%call _ := fifoEnq instr on addMultiplyFromImem in
     pass
  }}.

Definition addMultiplyFetch :=
  guard
    {{ fun st => bool_decide (st.(addMultiplySt) = State__Fetch) }}
    {{ let%read pc := addMultiplyPc in
       let%call _ := fifoEnq pc on addMultiplyToImem in
       let%write _ := State__Decode on addMultiplySt in
       pass
    }}.

Definition addMultiplyDecode :=
  guard
    {{ fun st => bool_decide (st.(addMultiplySt) = State__Decode) }}
    {{ let%read d2e      := addMultiplyDInstr in
       let%read rf       := addMultiplyRf in
       let%call instr    := fifoFirst on addMultiplyFromImem in
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
     let%modify _ := snoc (ImplLeak__Pc pc) on addMultiplyTrace in
     let%modify _ := snoc ImplLeak__Add on addMultiplyTrace in
     let%modify _ := fun pc => (pc `+Z` 4)%bv on addMultiplyPc in
     pass
  }}.

Definition addMultiplyExecuteNop :=
  {{ let%read pc := addMultiplyPc in
     let%call _ := fifoDeq on addMultiplyDInstr in
     let%write _ := State__Fetch on addMultiplySt in
     let%modify _ := snoc (ImplLeak__Pc pc) on addMultiplyTrace in
     let%modify _ := snoc ImplLeak__Nop on addMultiplyTrace in
     let%modify _ := fun pc => (pc `+Z` 4)%bv on addMultiplyPc in
     pass
  }}.

Definition addMultiplyExecuteMul rd v1 v2 :=
  {{ let%read pc := addMultiplyPc in
     let%read st := (multiplierSt ∘ addMultiplyM) in
     match st with
     | State__Empty =>
         let%call _ := multiplierEnq v1 v2 on addMultiplyM in
         pass
     | State__Busy =>
         let%call _ := multiplierRule on addMultiplyM in
         pass
     | State__Full =>
         let%call v := multiplierDeq on addMultiplyM in
         let%call _ := fifoDeq on addMultiplyDInstr in
         let%call _ := regFileUpd rd (truncate v) on addMultiplyRf in
         let%write _ := State__Fetch on addMultiplySt in
         let%modify _ := snoc (ImplLeak__Pc pc) on addMultiplyTrace in
         let%modify _ := snoc (ImplLeak__Mul v1) on addMultiplyTrace in
         let%modify _ := fun pc => (pc `+Z` 4)%bv on addMultiplyPc in
         pass
     end
  }}.

Definition addMultiplyExecute :=
  guard
    {{ fun st => bool_decide (st.(addMultiplySt) = State__Execute) }}
    {{ let%call instr := fifoFirst on addMultiplyDInstr in
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
    circuitResult m :=
      match m with
      | GetIReq => Bit 32
      | _ => unit
      end;
    circuitCall m :=
      match m with
      | GetIReq => addMultiplyGetIReq
      | GetIResp resp => addMultiplyGetIResp resp
      | Rule => addMultiplyRule
      end;
    circuitTrace := addMultiplyTrace
  |}.

Section example.
  Definition runCircuit := runCircuit addMultiplyCircuit.

  Example ex0 := mkAddMultiply.

  Eval vm_compute in ex0.

  Example ex1 :=
    runCircuit
      [Rule; GetIReq; GetIResp (Addi 1%bv 0%bv 3%bv); Rule;
       Rule; Rule; GetIReq; GetIResp (Addi 2%bv 0%bv 4%bv);
       Rule; Rule; Rule; GetIReq; GetIResp (Mul 3%bv 1%bv 2%bv);
       Rule; Rule; Rule; Rule; Rule; Rule; Rule; Rule; Rule;
       GetIReq; GetIResp (Mul 4%bv 3%bv 2%bv); Rule; Rule;
       Rule; Rule; Rule; Rule; Rule; Rule
      ].

  Eval vm_compute in ex1.
End example.
