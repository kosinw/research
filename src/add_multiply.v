From research Require Import base bit circuit multiplier fifo regfile.
From stdpp Require Import fin finite.

Notation Maybe := @option.

Inductive Instr :=
| Add (rd rs1 rs2 : Bit 5)
| Addi (rd rs1 : Bit 5) (imm : Bit 4)
| Mul (rd rs1 rs2 : Bit 5)
| Unknown.

Inductive method :=
| GetIReq
| GetIResp (resp : Instr)
| Rule.

Inductive state :=
| State__Fetch
| State__Decode
| State__Execute.

Inductive implLeakage := .

Instance state__EqDecision : EqDecision state.
Proof.
  solve_decision.
Defined.

Module AddMultiply.
  Inductive D2E :=
  | DAdd (rd : Bit 5) (v1 v2 : Bit 4)
  | DMul (rd : Bit 5) (v1 v2 : Bit 4).

  Record t :=
    { m : Multiplier.t
    ; rf : RegFile.t 4 5
    ; pc : Bit 32
    ; fromImem : Fifo.t Instr
    ; toImem : Fifo.t (Bit 32)
    ; d2e : Fifo.t D2E
    ; st : state
    ; trace : list implLeakage
    }.

  Definition mk :=
    {| m := Multiplier.mk
    ; rf := RegFile.mk
    ; pc := 0%bv
    ; fromImem := Fifo.mk
    ; toImem := Fifo.mk
    ; d2e := Fifo.mk
    ; st := State__Fetch
    ; trace := []
    |}.

  Definition getIReq :=
    {{ let%read toImem0 := toImem in
       if (Fifo.notEmpty toImem0) then
         let%call d := Fifo.deq on toImem in
         match d with
         | Valid d => ret d
         | Invalid => ret 0%bv
         end
       else
         ret 0%bv
    }}.

  Definition getIResp instr :=
    {{ let%read fromImem0 := fromImem in
       guard (Fifo.notFull fromImem0) then
         let%call _ := Fifo.enq instr on fromImem in
         pass
    }}.

  Definition fetch :=
    {{ let%read pc0 := pc in
       let%read toImem0 := toImem in
       guard (Fifo.notFull toImem0) then
         let%call _ := Fifo.enq pc0 on toImem in
         let%write st := State__Decode in
         pass
    }}.

  Definition decode :=
    {{ let%read fromImem0 := fromImem in
       let%read toImem0   := toImem in
       let%read d2e0      := d2e in
       let%read rf0       := rf in
       guard (Fifo.notFull d2e0 && Fifo.notEmpty fromImem0 && Fifo.notFull toImem0) then
         let%call instr := Fifo.deq on fromImem in
         match instr with
         | Valid Unknown =>
             let%write st := State__Fetch in pass
         | Valid (Add rd rs1 rs2) =>
             let v1 := RegFile.sub rs1 rf0 in
             let v2 := RegFile.sub rs2 rf0 in
             let%call _ := Fifo.enq (DAdd rd v1 v2) on d2e in
             let%write st := State__Execute in
             pass
         | Valid (Mul rd rs1 rs2) =>
             let v1 := RegFile.sub rs1 rf0 in
             let v2 := RegFile.sub rs2 rf0 in
             let%call _ := Fifo.enq (DMul rd v1 v2) on d2e in
             let%write st := State__Execute in
             pass
         | Valid (Addi rd rs1 imm) =>
             let v1 := RegFile.sub rs1 rf0 in
             let%call _ := Fifo.enq (DAdd rd v1 imm) on d2e in
             let%write st := State__Execute in
             pass
         | Invalid => pass
         end
    }}.

  Definition executeAdd rd v1 v2 :=
    {{ let%call _ := Fifo.deq on d2e in
       let%call _ := RegFile.upd rd (v1 + v2)%bv on rf in
       let%write st := State__Fetch in
       let%modify pc := fun pc => (pc `+Z` 4)%bv in
       pass
    }}.

  Definition executeMul rd v1 v2 :=
    {{ let%read m0 := m in
       match Multiplier.st m0 with
       | State__Empty =>
           let%call _ := Multiplier.enq v1 v2 on m in
           pass
       | State__Busy =>
           let%call _ := Multiplier.rule on m in
           pass
       | State__Full =>
           let%call v := Multiplier.deq on m in
           match v with
           | Valid v =>
               let%call _ := Fifo.deq on d2e in
               let%call _ := RegFile.upd rd (truncate v) on rf in
               let%write st := State__Fetch in
               let%modify pc := fun pc => (pc `+Z` 4)%bv in
               pass
           | Invalid => pass
           end
       end
    }}.

  Definition execute :=
    {{ let%read d2e0 := d2e in
       guard (Fifo.notEmpty d2e0) then
         let instr := Fifo.first d2e0 in
         match instr with
         | Valid (DAdd rd v1 v2) => executeAdd rd v1 v2
         | Valid (DMul rd v1 v2) => executeMul rd v1 v2
         | Invalid => pass
         end
    }}.

  Definition rule :=
    {{ let%read st0 := st in
       match st0 with
       | State__Fetch => fetch
       | State__Decode => decode
       | State__Execute => execute
       end
    }}.

  Instance circuit : Circuit :=
    {| circuitInit := mk
    ; circuitResult m :=
        match m with
        | GetIReq => Bit 32
        | GetIResp _ => unit
        | Rule => unit
        end
    ; circuitCall m :=
        match m with
        | GetIReq => getIReq
        | GetIResp resp => getIResp resp
        | Rule => rule
        end
    ; circuitTrace := trace
    |}.
End AddMultiply.

Section example.
  Notation runCircuit := (runCircuit (c := AddMultiply.circuit)).

  Definition ms :=
    [Rule
     ; GetIReq
     ; GetIResp (Addi 1%bv 0%bv 3%bv)
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; Rule
     ; GetIResp (Addi 2%bv 0%bv 4%bv)
     ; GetIReq
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
    ].

  Eval vm_compute in runCircuit ms.
End example.
