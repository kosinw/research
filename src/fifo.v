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

Definition fifoLift {t1 t2} (rel : t1 -> t2 -> Prop) (fifo1 : Fifo t1) (fifo2 : Fifo t2) :=
  match fifo1.(fifoContents), fifo2.(fifoContents) with
  | Some v1, Some v2 => rel v1 v2
  | None, None => True
  | _, _ => False
  end.

(* Hints about fifoLift. *)
Lemma hintFifoLift1 {t1 t2} : forall (q1 : Fifo t1) (q2 : Fifo t2) rel,
    q1.(fifoContents) = None ->
    q2.(fifoContents) <> None ->
    ~ fifoLift rel q1 q2.
Proof.
  cbv [ fifoLift] in *; simplify.
  repeat case_match; equality.
Qed.

Lemma hintFifoLift2 {t1 t2} : forall (q1 : Fifo t1) (q2 : Fifo t2) rel,
    q1.(fifoContents) <> None ->
    q2.(fifoContents) = None ->
    ~ fifoLift rel q1 q2.
Proof.
  cbv [ fifoLift] in *; simplify.
  repeat case_match; equality.
Qed.

Global Hint Resolve hintFifoLift1 hintFifoLift2 : core.
