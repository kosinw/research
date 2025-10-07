(**********************************************************************************)
(*                                                                                *)
(*             multiplier.v - Shift-and-add 4-bit multiplier.                     *)
(*                                                                                *)
(*                   +---------------------------+                                *)
(*                   |                           |                                *)
(*           A -----------                 ------|------ P                        *)
(*                   |                           |                                *)
(*           B -----------        A*B            |                                *)
(*                   |                           |                                *)
(*           V -----------                 ------------- R                        *)
(*                   |                           |                                *)
(*                   +---------------------------+                                *)
(*                                                                                *)
(*  The main theorem is a statement of a cryptographic constant-time (CCT)        *)
(*  hyperproperty. The statement of the property looks as follows (which we       *)
(*  state as an equivalent single-copy trace property):                           *)
(*                                                                                *)
(*  There exists some predictor [f] such that given a circuit_step schedule [C],         *)
(*  starting from a reset state, the multiplier circuit [M] will produce an       *)
(*  implementation leakage trace [t'].                                            *)
(*                                                                                *)
(*  A specification leakage trace [t] is extracted from schedule [C] which        *)
(*  will record the values of [A] and [valid] each circuit_step. On termination,         *)
(*                                                                                *)
(*                              [t' = f t].                                       *)
(*                                                                                *)
(**********************************************************************************)

From research Require Import base bitvector.

Local Open Scope bv_scope.

Section definitions.
  Record Registers :=
    { r_A : bv 8
    ; r_B : bv 4
    ; r_cnt : bv 2
    ; r_busy : bv 1
    }.

  Record I :=
    { in_A : bv 4
    ; in_B : bv 4
    ; in_valid : bv 1
    }.

  Record O :=
    { out_P : bv 8
    ; out_ready : bv 1
    }.

  Definition O0 := {| out_P := 0; out_ready := 0 |}.

  Record ILeakage :=
    { leak_valid : bv 1
    ; leak_ready : bv 1
    }.

  Record State :=
    { R : Registers
    ; T : list ILeakage
    ; Y : list O
    }.

  Definition State0 :=
    {| R := {| r_A := 0; r_B := 0; r_cnt := 0; r_busy := 0 |}
    ; T := []
    ; Y := [] |}.

  Definition shift_and_add (b : bv 4) (a : bv 8) : bv 8 :=
    let t0 := bv_extract 4 5 a in
    let t1 := if a? then 5#b else 0 in
    t0 + t1 || bv_extract 1 3 a.

  Definition circuit_step (s : State) (x : I) : State :=
    if s.(R).(r_busy) =? 0
    then
      if x.(in_valid) =? 1
      then
        let ra' := 8#x.(in_A) in
        let rb' := x.(in_B) in
        let rcount' := 3 in
        let rbusy' := 1 in
        let r' := {| r_A := ra'; r_B := rb'; r_cnt := rcount'; r_busy := rbusy' |} in
        let t' := s.(T) ++ [{| leak_valid := 1; leak_ready := 0 |}] in
        let y' := s.(Y) ++ [O0] in
        {| R := r'; T := t'; Y := y' |}
      else
        let t' := s.(T) ++ [{| leak_valid := 0; leak_ready := 0 |}] in
        let r' := s.(R) in
        let y' := s.(Y) ++ [O0] in
        {| R := r'; T := t'; Y := y' |}
    else
      let ra' := shift_and_add s.(R).(r_B) s.(R).(r_A) in
      let rb' := s.(R).(r_B) in
      if s.(R).(r_cnt) =? 0
      then
        let rcount' := 0 in
        let rbusy' := 0 in
        let r' := {| r_A := ra'; r_B := rb'; r_cnt := rcount'; r_busy := rbusy' |} in
        let t' := s.(T) ++ [{| leak_valid := x.(in_valid); leak_ready := 1 |}] in
        let y' := s.(Y) ++ [{| out_P := ra'; out_ready := 1 |}] in
        {| R := r'; T := t'; Y := y' |}
      else
        let rcount' := bv_pred s.(R).(r_cnt) in
        let rbusy' := 1 in
        let r' := {| r_A := ra'; r_B := rb'; r_cnt := rcount'; r_busy := rbusy' |} in
        let t' := s.(T) ++ [{| leak_valid := x.(in_valid); leak_ready := 0 |}] in
        let y' := s.(Y) ++ [O0] in
        {| R := r'; T := t'; Y := y' |}.

  Definition circuit_steps s xs := fold_left circuit_step xs s.
End definitions.

Section correctness.
  Fixpoint repeat {A : Type} (f : A -> A) (n : nat) {struct n} : (A -> A) :=
    match n with
    | 0%nat => id
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
    unfold Z.of_N, bv_odd.
    unfold bv_wrap. rewrite Zmod_odd. case_match.
    - replace (1 * bv_unsigned b)%Z with (bv_unsigned b) by lia. bv_solve.
    - Search (0 * _)%Z. rewrite Z.mul_0_l. bv_solve.
  Qed.

  Lemma shift_and_add_repeat_equiv : forall n a b,
      (repeat_shift_and_add' n) (bv_unsigned b) (bv_unsigned a) =
        bv_unsigned (repeat_shift_and_add n b a).
  Proof.
    intros n a b. induction n; simplify.
    - unfold repeat_shift_and_add', repeat_shift_and_add. equality.
    - unfold repeat_shift_and_add', repeat_shift_and_add in *. simplify.
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
  Ltac by_cases16 :=
    repeat match goal with
      | [ H : (0 <= ?z < 16)%Z |- _ ] =>
          let Hz := fresh "Hcases" in
          assert (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/
                    z = 8 \/ z = 9 \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15)%Z
            as Hz by lia; clear H;
          destruct_or?; subst
      end; equality.

  Lemma shift_and_add4'_multiplies : forall a b,
      (0 <= a < bv_modulus 4%N)%Z ->
      (0 <= b < bv_modulus 4%N)%Z ->
      shift_and_add4' b a = (a * b)%Z.
  Proof.
    intros a b Ha Hb.
    replace (bv_modulus 4%N) with 16%Z in * by reflexivity.
    by_cases16.
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
    - apply shift_and_add4_multiplies.
    - bv_saturate_unsigned. unfold bv_modulus in *; simplify. nia.
  Qed.

  Definition busy (s : State) := s.(R).(r_busy) = 1.
  Definition finished (s : State) := s.(R).(r_cnt) = 0.
  Definition valid (x : I) := x.(in_valid) = 1.

  Definition circuit_step_idle_valid s1 x s2 : Prop :=
    ~ busy s1 -> valid x -> s2 = circuit_step s1 x ->
    s2 = s1 <| R := {| r_A := 8#x.(in_A); r_B := x.(in_B); r_cnt := 3; r_busy := 1 |} |>
            <| T := s1.(T) ++ [{| leak_valid := 1; leak_ready := 0 |}] |>
            <| Y := s1.(Y) ++ [O0] |>.

  Lemma circuit_step_idle_valid_holds : forall s1 x s2, circuit_step_idle_valid s1 x s2.
  Proof.
    unfold circuit_step_idle_valid. simplify.
    unfold circuit_step in *. unfold busy in *.
    unfold valid in *. rewrite <- bv_eqb_neq in H.
    simplify!. rewrite H0. rewrite H.
    simplify. equality.
  Qed.

  Definition circuit_step_idle_invalid s1 x s2 : Prop :=
    ~ busy s1 -> ~ valid x -> s2 = circuit_step s1 x ->
    s2 = s1 <| T := s1.(T) ++ [{| leak_valid := 0; leak_ready := 0 |}] |>
            <| Y := s1.(Y) ++ [O0] |>.

  Lemma circuit_step_idle_invalid_holds : forall s1 x s2, circuit_step_idle_invalid s1 x s2.
  Proof.
    unfold circuit_step_idle_invalid. simplify.
    unfold circuit_step, busy, valid in *.
    simplify!. rewrite H. rewrite H0.
    simplify. equality.
  Qed.

  Definition circuit_step_busy_unfinished s1 x s2 : Prop :=
    busy s1 -> ~ finished s1 -> s2 = circuit_step s1 x ->
    s2 = s1 <| R; r_A := shift_and_add s1.(R).(r_B) s1.(R).(r_A) |>
            <| R; r_cnt := bv_pred s1.(R).(r_cnt)|>
            <| T := s1.(T) ++ [{| leak_valid := x.(in_valid); leak_ready := 0 |}] |>
            <| Y := s1.(Y) ++ [O0] |> .

  Lemma circuit_step_busy_unfinished_holds : forall s1 x s2, circuit_step_busy_unfinished s1 x s2.
  Proof.
    unfold circuit_step_busy_unfinished. simplify.
    unfold circuit_step, busy, finished in *.
    simplify!. rewrite H.
    simplify. rewrite <- bv_eqb_neq in H0. rewrite H0.
    equality.
  Qed.

  Definition circuit_step_busy_finished s1 x s2 : Prop :=
    busy s1 -> finished s1 -> s2 = circuit_step s1 x ->
    s2 = s1 <| R; r_A := shift_and_add s1.(R).(r_B) s1.(R).(r_A) |>
            <| R; r_cnt := 0 |>
            <| R; r_busy := 0 |>
            <| T := s1.(T) ++ [{| leak_valid := x.(in_valid); leak_ready := 1 |}] |>
            <| Y := s1.(Y) ++ [{|
                             out_P := shift_and_add s1.(R).(r_B) s1.(R).(r_A);
                             out_ready := 1
                           |}]
              |>.

  Lemma circuit_step_busy_finished_holds : forall s1 x s2, circuit_step_busy_finished s1 x s2.
  Proof.
    unfold circuit_step_busy_finished. simplify.
    unfold circuit_step, busy, finished in *.
    rewrite H0. simplify!. rewrite H.
    simplify. equality.
  Qed.

  Tactic Notation "unfold*" :=
    unfold circuit_step_idle_valid, circuit_step_idle_invalid, circuit_step_busy_unfinished,
      circuit_step_busy_finished, circuit_steps, busy, finished, shift_and_add4,
      valid, repeat_shift_and_add, repeat, compose in *.

  (* Finally, with all those helper theorems out of the way, we can now prove
     the following correctness property:

     For any circuit_step where the circuit is idle, if a valid [a] and [b] are
     provided, four circuit_steps later it will produce [a *| b]. *)

  Theorem circuit_steps_correct: forall s1 x1 s2 x2 s3 x3 s4 x4 s5 x5 s6 a b,
      ~ busy s1 ->
      x1 = {| in_A := a; in_B := b; in_valid := 1 |} ->
      s2 = circuit_step s1 x1 ->
      s3 = circuit_step s2 x2 ->
      s4 = circuit_step s3 x3 ->
      s5 = circuit_step s4 x4 ->
      s6 = circuit_step s5 x5 ->
      s6.(Y) = s1.(Y) ++ [O0; O0; O0; O0; {| out_P := a *| b; out_ready := 1 |}].
  Proof.
    intros. rewrite <- shift_and_add4_correct. unfold*. simpl in *.

    1: apply circuit_step_idle_valid_holds      in H1.
    1: apply circuit_step_busy_unfinished_holds in H2.
    1: apply circuit_step_busy_unfinished_holds in H3.
    1: apply circuit_step_busy_unfinished_holds in H4.
    1: apply circuit_step_busy_finished_holds   in H5.

    all: unfold*; simplify; solve [ eauto | bv_solve ].
  Qed.
End correctness.

Section ct.
  Definition SLeakage := option unit.

  Definition public1 x := if x.(in_valid) =? 1 then Some tt else None.

  Definition public := map public1.

  Definition PredictorState := option nat.

  Definition predictor_step (st : PredictorState) (s : SLeakage) :=
    match st with
    | Some (S n) => Some n
    | Some 0%nat => None
    | None =>
        match s with
        | Some _ => Some 3%nat
        | None   => None
        end
    end.

  Definition predictor_steps (st : PredictorState) (xs : list SLeakage) :=
    fold_left predictor_step xs st.

  Definition predict_next (st : PredictorState) (s : SLeakage) :=
    match st with
    | Some 0%nat =>
        match s with
        | Some _ => {| leak_valid := 1; leak_ready := 1 |}
        | None => {| leak_valid := 0; leak_ready := 1 |}
        end
    | _ =>
        match s with
        | Some _ => {| leak_valid := 1; leak_ready := 0 |}
        | None => {| leak_valid := 0; leak_ready := 0 |}
        end
    end.

  Fixpoint predict' st xs :=
    match xs with
    | [] => []
    | x :: xs' => predict_next st x :: predict' (predictor_step st x) xs'
    end.

  Definition predict xs := predict' None xs.

  Definition rep (x : State) (y : PredictorState) : Prop :=
    (exists v, y = Some v /\
            bv_unsigned x.(R).(r_cnt) = (Z.of_nat v) /\
            (v <= 3)%nat /\
            x.(R).(r_busy) = 1
    )
    \/ (y = None /\ x.(R).(r_busy) = 0).

  Lemma simulation_step : forall s1 s2 s1' s2' x,
      rep s1 s2 ->
      s1' = circuit_step s1 x ->
      s2' = predictor_step s2 (public1 x) ->
      rep s1' s2'.
  Proof.
    unfold rep, circuit_step, predictor_step, public1.
    simplify. inv H.
    - inv H0 as [v]. inv H. inv H1. inv H0. destruct v as [| v'].
      + assert (s1.(R).(r_cnt) = 0) by bv_solve.
        right. rewrite H0. rewrite H2. equality.
      + left. exists v'. intuition; try lia.
        * rewrite H2. simplify. pose proof H.
          apply bv_not_zero_nat_succ in H.
          rewrite <- bv_eqb_eq in H.
          apply not_true_is_false in H.
          replace 0 with (bv_0 2) by bv_solve.
          rewrite H. simplify. bv_simplify.
          rewrite H0. unfold bv_wrap, bv_modulus.
          lia.
        * rewrite H2. simplify. pose proof H.
          apply bv_not_zero_nat_succ in H.
          rewrite <- bv_eqb_eq in H.
          apply not_true_is_false in H.
          replace 0 with (bv_0 2) by bv_solve.
          rewrite H. simplify. equality.
    - inv H0. rewrite H1. simplify. repeat case_match; try equality.
      left. exists 3%nat. intuition.
  Qed.

  Lemma simulation_initial : rep State0 None.
  Proof.
    unfold rep. simplify. right. equality.
  Qed.

  Lemma simulation_many_step : forall xs s1 s2 s1' s2',
    rep s1 s2 ->
    s1' = circuit_steps s1 xs ->
    s2' = predictor_steps s2 (public xs) ->
    rep s1' s2'.
  Proof.
    induction xs as [| y ys IHy ]; simplify; try equality.
    - assert (rep (circuit_step s1 y) (predictor_step s2 (public1 y))).
      { apply simulation_step with (s1 := s1) (s2 := s2) (x := y); eauto. }
      unfold circuit_steps, predictor_steps. eapply IHy; eauto.
  Qed.

  Definition leak_next (s : State) (x : I) :=
    let ready :=
      if s.(R).(r_busy) =? 1
      then
        if s.(R).(r_cnt) =? 0
        then 1
        else 0
      else 0
    in
    {| leak_valid := x.(in_valid); leak_ready := ready |}.

  Lemma simulation_predict_leak : forall s1 s2 x,
      rep s1 s2 ->
      leak_next s1 x = predict_next s2 (public1 x).
  Proof.
    unfold leak_next, predict_next, public1, rep.
    simplify. inv H.
    - inv H0. inv H. inv H1. inv H0. destruct x0 as [| z].
      + assert (s1.(R).(r_cnt) = 0) by bv_solve.
        destruct s1. destruct R0. simplify.
        assert (in_valid x = 0 \/ in_valid x = 1).
        { apply bv_1_ind with (P := (fun x => x = 0 \/ x = 1)); eauto. }
        inv H0.
        * rewrite H2; simplify. equality.
        * rewrite H2; simplify. equality.
      + apply bv_not_zero_nat_succ in H. destruct s1.
        destruct R0. simplify. rewrite <- bv_eqb_neq in H.
        replace 0 with (bv_0 2) by bv_solve. rewrite H.
        assert (in_valid x = 0 \/ in_valid x = 1).
        { apply bv_1_ind with (P := (fun x => x = 0 \/ x = 1)); eauto. }
        inv H0.
        * rewrite H2; simplify. equality.
        * rewrite H2; simplify. equality.
    - inv H0. assert (in_valid x = 0 \/ in_valid x = 1).
      { apply bv_1_ind with (P := (fun x => x = 0 \/ x = 1)); eauto. }
      inv H.
      + rewrite H0. simplify. destruct s1. destruct R0. simplify.
        equality.
      + rewrite H0. simplify. destruct s1. destruct R0. simplify.
        equality.
  Qed.

  Lemma predict_app' : forall xs ys1 ys2 x s,
      ys1 = predict' s xs ->
      ys2 = predict' s (xs ++ [x]) ->
      ys2 = ys1 ++ [predict_next (predictor_steps s xs) x].
  Proof.
    induction xs as [| z zs IHz ]; simplify.
    - equality.
    - f_equal. apply IHz; equality.
  Qed.

  Lemma predict_app : forall xs x,
      predict (xs ++ [x]) =
        predict xs ++ [predict_next (predictor_steps None xs) x].
  Proof.
    simplify. apply predict_app'; equality.
  Qed.

  Lemma circuit_steps_app' : forall xs x s1 s2 s3,
      s2 = circuit_steps s1 xs ->
      s3 = circuit_steps s1 (xs ++ [x]) ->
      s3.(T) = s2.(T) ++ [leak_next s2 x].
  Proof.
    induction xs as [| z zs IHz ]; simplify.
    - unfold circuit_step, leak_next.
      destruct s1 as [R T Y]. destruct R as [a b count busy].
      simplify. repeat case_match; simplify!; eauto.
      all: try rewrite H0; eauto.
    - apply IHz with (s1 := (circuit_step s1 z)); equality.
  Qed.


  Lemma circuit_steps_app : forall xs x,
      T (circuit_steps State0 (xs ++ [x])) =
        T (circuit_steps State0 xs) ++ [leak_next (circuit_steps State0 xs) x].
  Proof.
    simplify. apply circuit_steps_app' with (xs := xs) (s1 := State0); equality.
  Qed.

  Theorem circuit_ct : exists f, forall xs s,
      s = circuit_steps State0 xs -> s.(T) = f (public xs).
  Proof.
    exists predict.
    induction xs as [| z zs IHz ] using rev_ind; simplify.
    - equality.
    - rewrite circuit_steps_app. unfold public. rewrite map_app.
      simplify. rewrite predict_app. rewrite IHz by equality.
      unfold public. repeat f_equal. apply simulation_predict_leak.
      apply simulation_many_step with (xs := zs) (s1 := State0) (s2 := None).
      + apply simulation_initial.
      + equality.
      + equality.
  Qed.
End ct.
