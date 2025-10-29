From research Require Import base circuit.

Module Fifo.
  Section WithContext.
    Context (a : Type).

    Record t := { first : Maybe a }.

    Definition mk := {| first := Invalid |}.

    Definition notEmpty s := bool_decide (s.(first) <> Invalid).
    Definition notFull s := bool_decide (s.(first) = Invalid).

    Definition enq in__a :=
      {{ let%read first0 := first in
         guard decide (first0 = Invalid) then
           let%write first := Valid in__a in
           pass
      }}.

    Definition deq :=
      {{ let%read first0 := first in
         if decide (first0 <> Invalid) then
           let%write first := Invalid in
           ret first0
         else
           ret Invalid
      }}.
  End WithContext.

  Arguments mk {_}.
  Arguments enq {_} (_ _).
  Arguments deq {_} (_).
  Arguments notEmpty {_} (_).
  Arguments notFull {_} (_).
End Fifo.
