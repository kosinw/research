(** Multiplier2.v - Formalization about CCT proofs on multiplier circuits. *)

Set Implicit Arguments.

From Research Require Import Tactics Bits Monad.
From Stdlib Require Import Program List.

Import ListNotations.

(**********************************************************************************)
(*                                                                                *)
(*  Represents the implementation of a standard multicycle, shift-and-add 4-bit   *)
(*  multiplier.                                                                   *)
(*                                                                                *)
(*                   +---------------------------+                                *)
(*                   |                           |                                *)
(*           A -----------                 ------------- P                        *)
(*                   |                           |                                *)
(*           B -----------        A*B      ------------- R                        *)
(*                   |                           |                                *)
(*           V -----------                       |                                *)
(*                   |                           |                                *)
(*                   +---------------------------+                                *)
(*                                                                                *)
(*  The main theorem is a statement of a cryptographic constant-time (CCT)        *)
(*  hyperproperty. The statement of the property looks as follows (which we state *)
(*  as an equivalent single-copy trace property):                                 *)
(*                                                                                *)
(*  There exists some predictor [f] such that given a cycle schedule [C],         *)
(*  starting from a reset state, the multiplier circuit [M] will produce an       *)
(*  implementation leakage trace [t'].                                            *)
(*                                                                                *)
(*  A specification leakage trace [t] is extracted from schedule [C] which        *)
(*  will record the values of [A] and [valid] each cycle. On termination,         *)
(*  the following invariant must hold [t' = f(t)].                                *)
(*                                                                                *)
(**********************************************************************************)

Module Basic.
  Local Open Scope bits_scope.

  Local Abbreviation W := 4%Z.
  Local Abbreviation WB := W.
  Local Abbreviation WA := (WB+WB)%Z.
  Local Abbreviation WCount := (Z.log2_up WB).

  (* First, we will define the state as the values of the internal registers. *)
  Record Registers :=
    mkRegisters
      { RA : bits WA
      ; RB : bits WB
      ; RCount : bits WCount
      ; RBusy : bits 1
      }.

  Definition R0 := mkRegisters 0 0 0 0.

  (* Then, we will augment the states of our transition system with
     implementation leakage traces. *)
  Record Leak :=
    mkLeak
      { LeakValid : bits 1
      ; LeakReady : bits 1
      }.

  Record State :=
    mkState
      { R : Registers
      ; T : list Leak
      }.

  Definition S0 := mkState R0 [].

  Local Definition StateM := (@Monad.StateM State).

  (* Now, we will state the input/output interface for our circuit. *)
  Record In :=
    mkIn
      { InA : bits W
      ; InB : bits W
      ; InValid : bits 1
      }.

  Definition I0 := mkIn 0 0 0.

  Fixpoint waitn (n : nat) : list In :=
    match n with
    | O => []
    | S n' => I0 :: waitn n'
    end.

  Notation "'in1' a b" := (mkIn a b 1) (at level 10, a at level 9, b at level 9).
  Notation "'in0'" := I0.

  Record Out :=
    mkOut
      { OutP : bits WA
      ; OutReady : bits 1 }.

  Definition O0 := mkOut 0 0.

  (* One shift-and-add micro-step: conditionally add `b` into the high half
     of `a` then shift-right by one by reassembly. *)
  Definition updateA (b : bits WB) (a : bits WA) : bits WA :=
    let t0 := zeroExtend (W+1) a.[WA-1,W] in
    let t1 := if a#[0] =? #1 then zeroExtend (W+1) b else 0 in
    ((t0 + t1) ## a.[W-1,1]).

  Definition cycle (inp : In) : StateM Out :=
    fun s =>
      if s.(R).(RBusy) =? 0
      then
        if inp.(InValid) =? 1
        then
          let ra' := zeroExtend WA inp.(InA) in
          let rb' := inp.(InB) in
          let rcount' := bits.of_Z WCount (W-1) in
          let rbusy' := #1 in
          let r' := mkRegisters ra' rb' rcount' rbusy' in
          let t' := s.(T) ++ [mkLeak inp.(InValid) 0 ] in
          let s' := mkState r' t' in
          (O0, s')
        else
            let t' := s.(T) ++ [mkLeak inp.(InValid) 0 ] in
            let r' := s.(R) in
            let s' := mkState r' t' in
            (O0, s')
      else
        let ra' := updateA s.(R).(RB) s.(R).(RA) in
        let rb' := s.(R).(RB) in
        if s.(R).(RCount) =? 0
        then
          let rcount' := 0 in
          let rbusy' := 0 in
          let r' := mkRegisters ra' rb' rcount' rbusy' in
          let t' := s.(T) ++ [mkLeak inp.(InValid) 1 ] in
          let s' := mkState r' t' in
          let o' := mkOut ra' 1 in
          (o', s')
        else
          let rcount' := s.(R).(RCount) - 1 in
          let rbusy' := #1 in
          let r' := mkRegisters ra' rb' rcount' rbusy' in
          let t' := s.(T) ++ [mkLeak inp.(InValid) 0 ] in
          let s' := mkState r' t' in
          (O0, s').

  Definition cycle' (inp : In) : State -> State :=
    Eval cbv beta iota zeta delta [ cycle compose snd ] in
      (snd ∘ cycle inp).

  Definition cycles : list In -> State -> State :=
    Eval cbv beta iota zeta delta [ fold_left flip cycle' ] in
      List.fold_left (flip cycle').

  Local Fixpoint selfCompose {A : Type} (n : nat) (f : A -> A) : (A -> A) :=
    match n with
    | O => id
    | S n' => f ∘ selfCompose n' f
    end.

  Lemma updateA_correct : forall (a b : Z) (q : bits WA),
      let a' := bits.of_Z WA a in
      let b' := bits.of_Z WB b in
      q = selfCompose (Z.to_nat W) (updateA b') a' ->
      q = bits.of_Z WA (a * b).
  Admitted.

  Hint Resolve updateA_correct : basic_db.

  Example ex1 :
    let s' := cycles (in1 #4 #5 :: waitn (Z.to_nat W)) S0 in
    s'.(R).(RBusy) = 0 /\ s'.(R).(RA) = #20.
  Proof. intuition equality. Qed.

  Example ex2 : forall (a b : Z),
      let s' := cycles (in1 (bits.of_Z W a) (bits.of_Z W b) :: waitn (Z.to_nat W)) S0 in
      s'.(R).(RBusy) = 0 /\ s'.(R).(RA) = bits.of_Z WA (a * b).
  Proof.
    intros a b; split; subst.
    - intuition equality.
    - apply updateA_correct with (a := a) (b := b).
      simplify. unfold compose; simplify.
      Search "zeroExtend". rewrite <- zeroExtend_of_Z.
      equality. linear_arithmetic.
  Qed.

  (* Now, we get to the statement of the main theorem, cryptographic constant time. *)
  Definition SLeak := option (bits W).

  Definition extract : list In -> list SLeak :=
    List.map (fun i => if i.(InValid) =? 1 then Some (i.(InA)) else None).
End Basic.
