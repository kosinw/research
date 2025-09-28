(**********************************************************************************)
(*                                                                                *)
(*  Standard multicycle, shift-and-add 4-bit multiplier.                          *)
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

From stdpp Require Import base numbers list tactics.
From research Require Import bitvector.
From RecordUpdate Require Import RecordUpdate.

Definition make_visible {X} (f : X) := f.

Notation "` f" := (make_visible f) (at level 10, format "` f").

Tactic Notation "unfold" "notation" constr(f) := change f with (`f).
Tactic Notation "fold" "notation" constr(f) := unfold make_visible.

Section Common.
  Record Registers :=
    mkRegisters
      { RA : bv 8
      ; RB : bv 4
      ; RCount : bv 2
      ; RBusy : bv 1
      }.

  Hint Constructors Registers : multiplier.

  Definition Registers0 := mkRegisters 0 0 0 0.

  Record In :=
    mkIn
      { InA : bv 4
      ; InB : bv 4
      ; InValid : bv 1
      }.

  Hint Constructors In : multiplier.

  Definition In0 := mkIn 0 0 0.

  Record Out :=
    mkOut
      { OutP : bv 8
      ; OutReady : bv 1 }.

  Hint Constructors Out : multiplier.

  Definition Out0 := mkOut 0 0.
End Common.

Module Basic.
  Local Open Scope bv_scope.

  Record ILeakage :=
    mkILeak
      { LeakValid : bv 1
      ; LeakReady : bv 1
      }.

  Hint Constructors ILeakage : multiplier.

  Record State :=
    mkState
      { R : Registers
      ; T : list ILeakage
      }.

  Hint Constructors State : multiplier.

  Definition State0 := mkState Registers0 [].

  (* One shift-and-add step: conditionally add `b` into the high half of `a`
     then shift-right by one by reassembly. *)
  Definition shift_and_add (b : bv 4) (a : bv 8) : bv 8 :=
    let t0 := bv_extract 4 5 a in
    let t1 := if bv_odd a then bv_zero_extend 5 b else 0 in
    bv_concat 8 (t0 + t1) (bv_extract 1 3 a).

  Definition cycle (s : State) (inp : In) : State * Out :=
    if s.(R).(RBusy) =? 0
    then
      if inp.(InValid) =? 1
      then
        let ra' := bv_zero_extend 8 inp.(InA) in
        let rb' := inp.(InB) in
        let rcount' := 3 in
        let rbusy' := 1 in
        let r' := mkRegisters ra' rb' rcount' rbusy' in
        let t' := s.(T) ++ [mkILeak inp.(InValid) 0 ] in
        let s' := mkState r' t' in
        (s', Out0)
      else
        let t' := s.(T) ++ [mkILeak inp.(InValid) 0 ] in
        let r' := s.(R) in
        let s' := mkState r' t' in
        (s', Out0)
    else
      let ra' := shift_and_add s.(R).(RB) s.(R).(RA) in
      let rb' := s.(R).(RB) in
      if s.(R).(RCount) =? 0
      then
        let rcount' := 0 in
        let rbusy' := 0 in
        let r' := mkRegisters ra' rb' rcount' rbusy' in
        let t' := s.(T) ++ [mkILeak inp.(InValid) 1 ] in
        let s' := mkState r' t' in
        let o' := mkOut ra' 1 in
        (s', o')
      else
        let rcount' := s.(R).(RCount) - 1 in
        let rbusy' := 1 in
        let r' := mkRegisters ra' rb' rcount' rbusy' in
        let t' := s.(T) ++ [mkILeak inp.(InValid) 0 ] in
        let s' := mkState r' t' in
        (s', Out0).

  Fixpoint cycles (s : State) (ins : list In) : State * list Out :=
    match ins with
    | [] => (s, [])
    | i :: ins' =>
        let (s', out) := cycle s i in
        let (s'', outs) := cycles s' ins' in
        (s', out :: outs)
    end.

  Fixpoint repeat {A : Type} (f : A -> A) (n : nat) {struct n} : (A -> A) :=
    match n with
    | O => id
    | S n' => f ∘ repeat f n'
    end.

  Definition repeat_shift_and_add n b a := (repeat (shift_and_add b) n) a.

  Definition shift_and_add4 := repeat_shift_and_add 4.

  Definition shift_and_add' (b a : Z) :=
    Z.lor (bv_wrap 5 (a ≫ 4 + (bv_wrap 1 a * b)) ≪ 3) (bv_wrap 3 (a ≫ 1)).

  Definition repeat_shift_and_add' n b a := (repeat (shift_and_add' b) n) a.

  Definition shift_and_add4' := repeat_shift_and_add' 4.

  Lemma shift_and_add_correct : forall a b,
      shift_and_add' (bv_unsigned b) (bv_unsigned a) =
        bv_unsigned (shift_and_add b a).
  Proof.
    intros a b. unfold shift_and_add, shift_and_add'. bv_simplify.
    unfold Z.of_N, bv_odd. unfold notation Z.modulo. Search (_ `mod` 2)%Z.
    unfold bv_wrap. rewrite Zmod_odd. case_match.
    - replace (1 * bv_unsigned b)%Z with (bv_unsigned b) by lia. bv_solve.
    - Search (0 * _)%Z. rewrite Z.mul_0_l. bv_solve.
  Qed.

  Lemma shift_and_add_repeat_correct : forall n a b,
      (repeat_shift_and_add' n) (bv_unsigned b) (bv_unsigned a) =
        bv_unsigned (repeat_shift_and_add n b a).
  Proof.
    intros n a b. induction n; simpl.
    - unfold repeat_shift_and_add', repeat_shift_and_add. done.
    - unfold repeat_shift_and_add', repeat_shift_and_add in *. simpl.
      rewrite IHn. apply shift_and_add_correct.
  Qed.

  Lemma shift_and_add4_correct : forall a b,
      shift_and_add4' (bv_unsigned b) (bv_unsigned a) =
        bv_unsigned (shift_and_add4 b a).
  Proof.
    unfold shift_and_add4', shift_and_add4. apply shift_and_add_repeat_correct.
  Qed.

  (* Tactic for exhaustive case analysis on integers in range [0,16) *)
  (* Automatically finds variables with range hypotheses and does case analysis *)
  Ltac case_range16 :=
    repeat match goal with
      | [ H : (0 <= ?z < 16)%Z |- _ ] =>
          let Hz := fresh "H_cases" in
          assert (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/
                    z = 8 \/ z = 9 \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15)%Z
            as Hz by lia; clear H;
          destruct_or?; subst
      end; done.

  Lemma shift_and_add4'_multiplies : forall a b,
      (0 <= a < bv_modulus 4%N)%Z ->
      (0 <= b < bv_modulus 4%N)%Z ->
      shift_and_add4' b a = (a * b)%Z.
  Proof.
    intros a b Ha Hb.
    replace (bv_modulus 4%N) with 16%Z in * by trivial.
    rewrite Z.mul_comm.
    case_range16.
  Qed.

  Lemma shift_and_add4_multiplies : forall (a b : bv 4),
      bv_unsigned (shift_and_add4 b (bv_zero_extend 8 a)) = (bv_unsigned a * bv_unsigned b)%Z.
  Proof.
    intros a b. rewrite <- shift_and_add4_correct.
    Search bv_unsigned bv_zero_extend. rewrite bv_zero_extend_unsigned.
    apply shift_and_add4'_multiplies. all: bv_solve.
  Qed.

  Lemma bv1_is_0_or_1 : forall (b : bv 1), b = 0 \/ b = 1.
  Proof.
    intro b. Search "bv" "ind".
    apply bv_1_ind with (P := (fun b => b = 0 \/ b = 1)); intuition congruence.
  Qed.

  Hint Resolve bv1_is_0_or_1 : multiplier.

  Definition busy (s : State) := s.(R).(RBusy) = 1.
  Definition valid (i : In) := i.(InValid) = 1.

  Hint Extern 1 (_ = _ :> bv 1) =>
         match goal with
         | |- ?b = 0 :> bv 1 => pose proof (bv1_is_0_or_1 b); intuition
         | |- ?b = 1 :> bv 1 => pose proof (bv1_is_0_or_1 b); intuition
         end : multiplier.

  Lemma cycle_idle_valid : forall s s' a b i o,
      ~ busy s -> valid i -> a = i.(InA) -> b = i.(InB) -> (s', o) = cycle s i ->
      s' = {| R := {| RA := 8#a; RB := b; RCount := 3; RBusy := 1 |};
             T := s.(T) ++ [{| LeakValid := 1; LeakReady := 0 |}]
        |} /\ o = Out0.
  Proof.
    repeat progress (intros; simpl; subst).
    unfold cycle in *. unfold bv_eqb in *. unfold busy in *.
    unfold valid in *. assert (s.(R).(RBusy) = 0) by auto with multiplier.
    repeat rewrite H1 in H3. simpl in *. rewrite H0 in H3.
    simpl in *. inversion H3; clear H3. subst. done.
  Qed.

  Lemma cycle_idle_invalid : forall s s' i o,
      ~ busy s -> ~ valid i -> (s', o) = cycle s i ->
      s' = {| R := s.(R); T := s.(T) ++ [{| LeakValid := 0; LeakReady := 0 |}] |}
      /\ o = Out0.
  Proof.
    repeat progress (intros; simpl; subst).
    unfold cycle, bv_eqb, busy, valid in *.
    assert (s.(R).(RBusy) = 0) by auto with multiplier.
    assert (i.(InValid) = 0) by auto with multiplier.
    rewrite H2, H3 in H1. simpl in *. inversion H1; clear H1.
    done.
  Qed.

  (** NOTE knwabueze for aerbsen: I think we talked about using this definition
      for the extraction from the list of inputs to the specification leakage.

    {[
        Definition SLeakage := bv 4.

        Definition extract : list In -> list SLeakage :=
          flat_map (fun i => if i.(InValid) =? 1 then [i.(InA)] else []).
    ]}

    However, I think this original definition is problematic. The predictor
    function would need to know whether or not a value for [A] was provided on
    each cycle, not just the total list of provided values. *)

  Definition SLeakage := option (bv 4).

  Definition extract : list In -> list SLeakage :=
    map (fun i => if i.(InValid) =? 1 then Some i.(InA) else None).

  Theorem ct : exists (predictor : list SLeakage -> list ILeakage),
    forall (s' : State) (is : list In) (os : list Out),
      (s', os) = cycles State0 is -> s'.(T) = (predictor ∘ extract) is.
  Admitted.
End Basic.
