From research Require Import base circuit.

Section WithContext.
  Context (a : Type) `{Default a}.

  Record Fifo := { fifoContents : option a }.
  Definition mkFifo := {| fifoContents := None |}.

  Definition fifoNotEmpty s := bool_decide (s.(fifoContents) <> None).

  Definition fifoNotFull s := bool_decide (s.(fifoContents) = None).

  Definition fifoEnq x1 :=
    guard
      {{ fifoNotFull }}
      {{ let%write _ := Some x1 on fifoContents in
         pass
      }}.

  Definition fifoDeq :=
    guard
      {{ fifoNotEmpty }}
      {{ let%write _ := None on fifoContents in
         pass
      }}.

  Definition fifoFirst st :=
    match st.(fifoContents) with
    | Some x => x
    | None => δ
    end.
End WithContext.

Arguments mkFifo {_}.
Arguments fifoEnq {_} (_ _).
Arguments fifoDeq {_} (_).
Arguments fifoFirst {_ _} (_).
