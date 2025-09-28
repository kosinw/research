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

From stdpp Require Import base tactics decidable.
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

  Definition Registers0 := mkRegisters 0 0 0 0.

  Record In :=
    mkIn
      { InA : bv 4
      ; InB : bv 4
      ; InValid : bv 1
      }.

  Definition In0 := mkIn 0 0 0.

  Record Out :=
    mkOut
      { OutP : bv 8
      ; OutReady : bv 1 }.

  Definition Out0 := mkOut 0 0.
End Common.

Module Circuit1.
  Local Open Scope bv_scope.

  Record ILeakage :=
    mkILeak
      { LeakValid : bv 1
      ; LeakReady : bv 1
      }.

  Record State :=
    mkState
      { R : Registers
      ; T : list ILeakage
      }.

  Definition State0 := mkState Registers0 [].

  (* One shift-and-add step: conditionally add `b` into the high half of `a`
     then shift-right by one by reassembly. *)
  Definition shift_and_add (b : bv 4) (a : bv 8) : bv 8 :=
    let t0 := bv_extract 4 5 a in
    let t1 := if bv_odd a then 5#b else 0 in
    bv_concat 8 (t0 + t1) (bv_extract 1 3 a).

  Definition cycle (s : State) (x : In) : State * Out :=
    if s.(R).(RBusy) =? 0
    then
      if x.(InValid) =? 1
      then
        let ra' := 8#x.(InA) in
        let rb' := x.(InB) in
        let rcount' := 3 in
        let rbusy' := 1 in
        let r' := mkRegisters ra' rb' rcount' rbusy' in
        let t' := s.(T) ++ [mkILeak x.(InValid) 0 ] in
        let s' := mkState r' t' in
        (s', Out0)
      else
        let t' := s.(T) ++ [mkILeak x.(InValid) 0 ] in
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
        let t' := s.(T) ++ [mkILeak x.(InValid) 1 ] in
        let s' := mkState r' t' in
        let o' := mkOut ra' 1 in
        (s', o')
      else
        let rcount' := s.(R).(RCount) - 1 in
        let rbusy' := 1 in
        let r' := mkRegisters ra' rb' rcount' rbusy' in
        let t' := s.(T) ++ [mkILeak x.(InValid) 0 ] in
        let s' := mkState r' t' in
        (s', Out0).

  Fixpoint cycles (s : State) (xs : list In) : State * list Out :=
    match xs with
    | [] => (s, [])
    | x :: xs' =>
        let (s', y) := cycle s x in
        let (s'', ys) := cycles s' xs' in
        (s'', y :: ys)
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

  Lemma shift_and_add_equiv : forall a b,
      shift_and_add' (bv_unsigned b) (bv_unsigned a) =
        bv_unsigned (shift_and_add b a).
  Proof.
    intros a b. unfold shift_and_add, shift_and_add'. bv_simplify.
    unfold Z.of_N, bv_odd. unfold notation Z.modulo. Search (_ `mod` 2)%Z.
    unfold bv_wrap. rewrite Zmod_odd. case_match.
    - replace (1 * bv_unsigned b)%Z with (bv_unsigned b) by lia. bv_solve.
    - Search (0 * _)%Z. rewrite Z.mul_0_l. bv_solve.
  Qed.

  Lemma shift_and_add_repeat_equiv : forall n a b,
      (repeat_shift_and_add' n) (bv_unsigned b) (bv_unsigned a) =
        bv_unsigned (repeat_shift_and_add n b a).
  Proof.
    intros n a b. induction n; simpl.
    - unfold repeat_shift_and_add', repeat_shift_and_add. done.
    - unfold repeat_shift_and_add', repeat_shift_and_add in *. simpl.
      rewrite IHn. apply shift_and_add_equiv.
  Qed.

  Lemma shift_and_add4_equiv : forall a b,
      shift_and_add4' (bv_unsigned b) (bv_unsigned a) =
        bv_unsigned (shift_and_add4 b a).
  Proof.
    unfold shift_and_add4', shift_and_add4. apply shift_and_add_repeat_equiv.
  Qed.

  (* Tactic for exhaustive case analysis on integers in range [0,16) *)
  (* Automatically finds variables with range hypotheses and does case analysis *)
  Ltac case_range16 :=
    repeat match goal with
      | [ H : (0 <= ?z < 16)%Z |- _ ] =>
          let Hz := fresh "Hcases" in
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
      bv_unsigned (shift_and_add4 b (8#a)) = (bv_unsigned a * bv_unsigned b)%Z.
  Proof.
    intros a b. rewrite <- shift_and_add4_equiv.
    Search bv_unsigned bv_zero_extend. rewrite bv_zero_extend_unsigned by lia.
    apply shift_and_add4'_multiplies. all: bv_solve.
  Qed.

  Notation "a *| b" := ((8#a) * (8#b)) (at level 35).

  Lemma shift_and_add4_correct : forall (a b : bv 4),
      shift_and_add4 b (8#a) = a *| b.
  Proof.
    intros a b. Search (bv_unsigned _ = bv_unsigned _).
    rewrite bv_eq. Search bv_mul.
    rewrite bv_mul_unsigned.
    Search bv_zero_extend bv_unsigned.
    repeat rewrite bv_zero_extend_unsigned by lia.
    Check bv_wrap_small. rewrite bv_wrap_small.
    apply shift_and_add4_multiplies. bv_saturate_unsigned.
    unfold bv_modulus in *; simpl in *. nia.
  Qed.

  Lemma bv1_is_0_or_1 : forall (b : bv 1), b = 0 \/ b = 1.
  Proof.
    intro b. Search "bv" "ind".
    apply bv_1_ind with (P := (fun b => b = 0 \/ b = 1)); intuition congruence.
  Qed.

  Definition busy (s : State) := s.(R).(RBusy) = 1.
  Definition finished (s : State) := s.(R).(RCount) = 0.
  Definition valid (x : In) := x.(InValid) = 1.

  Hint Extern 1 (_ = _ :> bv 1) =>
         match goal with
         | |- ?b = 0 :> bv 1 => pose proof (bv1_is_0_or_1 b); intuition
         | |- ?b = 1 :> bv 1 => pose proof (bv1_is_0_or_1 b); intuition
         end : multiplier.

  Definition cycle_idle_valid s1 x s2 y : Prop :=
      ~ busy s1 -> valid x -> (s2, y) = cycle s1 x ->
      (s2, y) = (s1 <| R := {| RA := 8#x.(InA); RB := x.(InB); RCount := 3; RBusy := 1 |} |>
                    <| T := s1.(T) ++ [{| LeakValid := 1; LeakReady := 0 |}] |>,
                 Out0).

  Lemma cycle_idle_valid_holds : forall s1 x s2 y, cycle_idle_valid s1 x s2 y.
  Proof.
    unfold cycle_idle_valid.
    repeat progress (intros; simpl; subst).
    unfold cycle in *. unfold bv_eqb in *. unfold busy in *.
    unfold valid in *. assert (s1.(R).(RBusy) = 0) by auto with multiplier.
    repeat rewrite H2 in H1. simpl in *. rewrite H0 in H1.
    csimpl in *. inv H1. done.
  Qed.

  Definition cycle_idle_invalid s1 x s2 y : Prop :=
    ~ busy s1 -> ~ valid x -> (s2, y) = cycle s1 x ->
    (s2, y) = (s1 <| T := s1.(T) ++ [{| LeakValid := 0; LeakReady := 0 |}] |>,
               Out0).

  Lemma cycle_idle_invalid_holds : forall s1 x s2 y, cycle_idle_invalid s1 x s2 y.
  Proof.
    unfold cycle_idle_invalid.
    repeat progress (intros; simpl; subst).
    unfold cycle, bv_eqb, busy, valid in *.
    assert (s1.(R).(RBusy) = 0) by auto with multiplier.
    assert (x.(InValid) = 0) by auto with multiplier.
    rewrite H2, H3 in H1. simpl in *. inversion H1; clear H1.
    done.
  Qed.

  Definition cycle_busy_unfinished s1 x s2 y : Prop :=
    busy s1 -> ~ finished s1 -> (s2, y) = cycle s1 x ->
      (s2, y) = (s1 <| R; RA := shift_and_add s1.(R).(RB) s1.(R).(RA) |>
                    <| R; RCount := s1.(R).(RCount) - 1 |>
                   <| T := s1.(T) ++ [{| LeakValid := x.(InValid); LeakReady := 0 |}] |>,
                 Out0).

  Lemma cycle_busy_unfinished_holds : forall s1 x s2 y, cycle_busy_unfinished s1 x s2 y.
  Proof.
    unfold cycle_busy_unfinished.
    repeat progress (intros; simpl; subst).
    unfold cycle, bv_eqb, busy, finished in *.
    rewrite H in H1; simpl in *.
    destruct (bv_eq_dec 2 (RCount (R s1)) 0) as [Heq | Hneq].
    - done.
    - inversion H1; clear H1; subst. intuition congruence.
  Qed.

  Definition cycle_busy_finished s1 x s2 y : Prop :=
    busy s1 -> finished s1 -> (s2, y) = cycle s1 x ->
      (s2, y) = (s1 <| R; RA := shift_and_add s1.(R).(RB) s1.(R).(RA) |>
                    <| R; RCount := 0 |>
                    <| R; RBusy := 0 |>
                    <| T := s1.(T) ++ [{| LeakValid := x.(InValid); LeakReady := 1 |}] |>,
                 {| OutP := s2.(R).(RA); OutReady := 1 |}).

  Lemma cycle_busy_finished_holds : forall s1 x s2 y, cycle_busy_finished s1 x s2 y.
  Proof.
    unfold cycle_busy_finished.
    repeat progress (intros; simpl; subst).
    unfold cycle, bv_eqb, busy, finished in *.
    rewrite H in H1; simpl in *. rewrite H0 in H1.
    simpl in *. inversion H1; clear H1; subst. done.
  Qed.

  Ltac simplify :=
    repeat progress (intros; csimpl in *; subst).

  Ltac unfold_cycle_predicates :=
    unfold cycle_idle_valid, cycle_idle_invalid, cycle_busy_unfinished,
      cycle_busy_finished, busy, finished, valid in *.

  Ltac unfold_pair H := inversion H; clear H.

  Ltac unfold_pairs :=
    repeat match goal with
      | H : (_, _) = (_, _) |- _ => unfold_pair H
      end.

  Ltac unroll_let e :=
    let Hlet := fresh "Hlet0" in destruct e eqn:Hlet; symmetry in Hlet.

  Ltac unroll_lets :=
    repeat match goal with
      | [ H : context[let (_, _) := (cycle ?x ?y) in _] |- _ ] =>
          unroll_let (cycle x y)
      end.

  Ltac cauto :=
    unfold_pairs; subst;
    try (unfold_cycle_predicates;
         solve [ naive_solver | csimpl in *; bv_solve ]).

  (* Finally, with all those helper theorems out of the way, we can now prove
     the following correctness property:

     For any cycle where the circuit is idle, if a valid [a] and [b] are
     provided, four cycles later it will produce [a *| b]. *)
  Theorem cycles_correct : forall s s' x1 x2 x3 x4 x5 ys a b,
      ~ busy s -> x1 = {| InA := a; InB := b; InValid := 1 |} ->
      (s', ys) = cycles s [x1; x2; x3; x4; x5] ->
      ys = [Out0; Out0; Out0; Out0; {| OutP := a *| b; OutReady := 1 |}].
  Proof.
    simplify. unroll_lets.
    apply cycle_idle_valid_holds in Hlet0; cauto.
    apply cycle_busy_unfinished_holds in Hlet1; cauto.
    apply cycle_busy_unfinished_holds in Hlet2; cauto.
    apply cycle_busy_unfinished_holds in Hlet3; cauto.
    apply cycle_busy_finished_holds in Hlet4; cauto.
    simplify. repeat f_equal. by apply shift_and_add4_correct.
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
    map (fun x => if x.(InValid) =? 1 then Some x.(InA) else None).

  Theorem cycles_ct : exists (predictor : list SLeakage -> list ILeakage),
    forall (xs : list In) (ys : list Out) (s : State),
      (s, ys) = cycles State0 xs -> s.(T) = (predictor ∘ extract) xs.
  Admitted.
End Circuit1.
