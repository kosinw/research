From research Require Import base bit circuit multiplier fifo regfile.
From stdpp Require Import fin finite.

Notation Maybe := @option.

Inductive Instr :=
| Add (rd rs1 rs2 : Bit 5)
| Addi (rd rs1 : Bit 5) (imm : Bit 4)
| Mul (rd rs1 rs2 : Bit 5)
| Unknown.

Instance defaultInstr : Default Instr := Unknown.

Inductive method :=
| GetIReq
| GetIResp (resp : Instr)
| Rule.

Inductive state :=
| State__Fetch
| State__Decode
| State__Execute.

Inductive implLeak :=
| ImplLeak__Pc (l : Bit 32)
| ImplLeak__Add
| ImplLeak__Mul (a : Bit 4).

Instance state__EqDecision : EqDecision state.
Proof.
  solve_decision.
Defined.

Inductive D2E :=
| DAdd (rd : Bit 5) (v1 v2 : Bit 4)
| DMul (rd : Bit 5) (v1 v2 : Bit 4).

Instance defaultD2E : Default D2E := DAdd 0%bv 0%bv 0%bv.

Record AddMultiply :=
  { addMultiplyM : Multiplier
  ; addMultiplyRf : RegFile 4 5
  ; addMultiplyPc : Bit 32
  ; addMultiplyFromImem : Fifo Instr
  ; addMultiplyToImem : Fifo (Bit 32)
  ; addMultiplyD2E : Fifo D2E
  ; addMultiplySt : state
  ; addMultiplyTrace : list implLeak
  }.

Definition mkAddMultiply :=
  {|
    addMultiplyM := mkMultiplier;
    addMultiplyRf := mkRegFile;
    addMultiplyPc := 0%bv;
    addMultiplyFromImem := mkFifo;
    addMultiplyToImem := mkFifo;
    addMultiplyD2E := mkFifo;
    addMultiplySt := State__Fetch;
    addMultiplyTrace := []
  |}.

Definition addMultiplyGetIReq :=
  {{ let%read toImem := addMultiplyToImem in
     if fifoNotEmpty toImem then
       let%call d := fifoDeq on addMultiplyToImem in
       ret d
     else
       ret 0%bv
  }}.

Definition addMultiplyGetIResp instr :=
  {{ let%read fromImem := addMultiplyFromImem in
     let%read toImem := addMultiplyToImem in
     when fifoNotFull fromImem && fifoNotFull toImem then
       let%call _ := fifoEnq instr on addMultiplyFromImem in
       pass
  }}.

Definition addMultiplyFetch :=
  {{ let%read pc := addMultiplyPc in
     let%read toImem := addMultiplyToImem in
     when fifoNotFull toImem then
       let%call _ := fifoEnq pc on addMultiplyToImem in
       let%write addMultiplySt := State__Decode in
       pass
  }}.

Definition addMultiplyDecode :=
  {{ let%read fromImem := addMultiplyFromImem in
     let%read toImem   := addMultiplyToImem in
     let%read d2e      := addMultiplyD2E in
     let%read rf       := addMultiplyRf in
     when fifoNotFull d2e && fifoNotEmpty fromImem && fifoNotFull toImem then
       let%call instr := fifoDeq on addMultiplyFromImem in
       match instr with
       | Unknown =>
           (* In this case, an unknown instruction is encounteted, could
              just send a no-op to the execution unit instead. *)
           let%write addMultiplySt := State__Fetch in pass
       | Add rd rs1 rs2 =>
           let v1 := regFileSub rs1 rf in
           let v2 := regFileSub rs2 rf in
           let%call _ := fifoEnq (DAdd rd v1 v2) on addMultiplyD2E in
           let%write addMultiplySt := State__Execute in
           pass
       | Mul rd rs1 rs2 =>
           let v1 := regFileSub rs1 rf in
           let v2 := regFileSub rs2 rf in
           let%call _ := fifoEnq (DMul rd v1 v2) on addMultiplyD2E in
           let%write addMultiplySt := State__Execute in
           pass
       | Addi rd rs1 imm =>
           let v1 := regFileSub rs1 rf in
           let%call _ := fifoEnq (DAdd rd v1 imm) on addMultiplyD2E in
           let%write addMultiplySt := State__Execute in
           pass
       end
  }}.

Definition addMultiplyExecuteAdd rd v1 v2 :=
  {{ let%read pc := addMultiplyPc in
     let%call _ := fifoDeq on addMultiplyD2E in
     let%call _ := regFileUpd rd (v1 + v2)%bv on addMultiplyRf in
     let%write addMultiplySt := State__Fetch in
     let%modify addMultiplyTrace := snoc (ImplLeak__Pc pc) in
     let%modify addMultiplyTrace := snoc ImplLeak__Add in
     let%modify addMultiplyPc := fun pc => (pc `+Z` 4)%bv in
     pass
  }}.

Definition addMultiplyExecuteMul rd v1 v2 :=
  {{ let%read m := addMultiplyM in
     let%read pc := addMultiplyPc in
     match m.(multiplierSt) with
     | State__Empty =>
         let%call _ := multiplierEnq v1 v2 on addMultiplyM in
         pass
     | State__Busy =>
         let%call _ := multiplierRule on addMultiplyM in
         pass
     | State__Full =>
         let%call v := multiplierDeq on addMultiplyM in
         match v with
         | Valid v =>
             let%call _ := fifoDeq on addMultiplyD2E in
             let%call _ := regFileUpd rd (truncate v) on addMultiplyRf in
             let%write addMultiplySt := State__Fetch in
             let%modify addMultiplyTrace := snoc (ImplLeak__Pc pc) in
             let%modify addMultiplyTrace := snoc (ImplLeak__Mul v1) in
             let%modify addMultiplyPc := fun pc => (pc `+Z` 4)%bv in
             pass
         | Invalid => pass
         end
     end
  }}.

Definition addMultiplyExecute :=
  {{ let%read d2e := addMultiplyD2E in
     when fifoNotEmpty d2e then
       let instr := fifoFirst d2e in
       match instr with
       | DAdd rd v1 v2 => addMultiplyExecuteAdd rd v1 v2
       | DMul rd v1 v2 => addMultiplyExecuteMul rd v1 v2
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
  {| circuitInit := mkAddMultiply
  ; circuitResult m :=
      match m with
      | GetIReq => Bit 32
      | _ => unit
      end
  ; circuitCall m :=
      match m with
      | GetIReq => addMultiplyGetIReq
      | GetIResp resp => addMultiplyGetIResp resp
      | Rule => addMultiplyRule
      end
  ; circuitTrace := addMultiplyTrace
  |}.

Section example.
  Definition ms :=
    [Rule
     ; GetIReq
     ; GetIResp (Addi 1%bv 0%bv 3%bv)
     ; Rule
     ; Rule
     ; Rule
     ; GetIReq
     ; GetIResp (Addi 2%bv 0%bv 4%bv)
     ; Rule
     ; Rule
     ; Rule
     ; GetIReq
     ; GetIResp (Mul 3%bv 1%bv 2%bv)
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; GetIReq
     ; GetIResp (Mul 4%bv 3%bv 2%bv)
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
    ].

  Eval vm_compute in runCircuit addMultiplyCircuit ms.
End example.
