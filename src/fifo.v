From research Require Import base circuit.

Section WithContext.
  Context (a : Type) `{Default a}.

  Record Fifo := { fifoContents : Maybe a }.
  Definition mkFifo := {| fifoContents := Invalid |}.

  Definition fifoNotEmpty s := bool_decide (s.(fifoContents) <> Invalid).

  Definition fifoNotFull s := bool_decide (s.(fifoContents) = Invalid).

  Definition fifoEnq x1 :=
    guard
      {{ fifoNotFull }}
      {{ let%write _ := Valid x1 on fifoContents in
         pass
      }}.

  Definition fifoDeq :=
    guard
      {{ fifoNotEmpty }}
      {{ let%write _ := Invalid on fifoContents in
         pass
      }}.

  Definition fifoFirst :=
    guard
      {{ fifoNotEmpty }}
      {{ let%read x := fifoContents in
         match x with
         | Valid x => ret x
         | Invalid => ret δ
         end
      }}.
End WithContext.

Arguments mkFifo {_}.
Arguments fifoEnq {_} (_ _).
Arguments fifoDeq {_} (_).
Arguments fifoFirst {_ _} (_).
