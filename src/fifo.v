From research Require Import base circuit.

Section WithContext.
  Context (a : Type) `{Default a}.

  Record Fifo := { fifoContents : Maybe a }.

  Definition mkFifo := {| fifoContents := Invalid |}.

  Definition fifoNotEmpty s := bool_decide (s.(fifoContents) <> Invalid).
  Definition fifoNotFull s := bool_decide (s.(fifoContents) = Invalid).

  Definition fifoEnq in__a :=
    {{ let%read first := fifoContents in
       when decide (first = Invalid) then
         let%write fifoContents := Valid in__a in
         pass
    }}.

  Definition fifoDeq :=
    {{ let%read first := fifoContents in
       let%write fifoContents := Invalid in
       match first with
       | Valid x => ret x
       | Invalid => ret δ
       end
    }}.

  Definition fifoFirst s :=
    match s.(fifoContents) with
    | Valid x => x
    | Invalid => δ
    end.
End WithContext.

Arguments mkFifo {_}.
Arguments fifoEnq {_} (_ _).
Arguments fifoDeq {_ _} (_).
Arguments fifoNotEmpty {_} (_).
Arguments fifoNotFull {_} (_).
