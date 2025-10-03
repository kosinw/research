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
(*  There exists some predictor [f] such that given a cycle schedule [C],         *)
(*  starting from a reset state, the multiplier circuit [M] will produce an       *)
(*  implementation leakage trace [t'].                                            *)
(*                                                                                *)
(*  A specification leakage trace [t] is extracted from schedule [C] which        *)
(*  will record the values of [A] and [valid] each cycle. On termination,         *)
(*                                                                                *)
(*                              [t' = f t].                                       *)
(*                                                                                *)
(**********************************************************************************)

From stdpp Require Import base tactics bitvector list.
From RecordUpdate Require Import RecordUpdate.

Local Open Scope bv_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Ltac simplify := repeat progress (intros; csimpl in *; subst).
Ltac equality := intuition congruence.

Definition make_visible {X} (f : X) := f.

Notation "` f" := (make_visible f) (at level 10, format "` f").

Tactic Notation "unfold" "notation" constr(f) := change f with (`f).
Tactic Notation "fold" "notation" constr(f) := unfold make_visible.

Definition bv_eqb {n} (x y : bv n) : bool :=
  Eval cbv delta [ bool_decide decide_rel ] in
    bool_decide (x = y).

Definition bv_odd {n} (x : bv n) := Z.odd (bv_unsigned x).

Infix "=?" := bv_eqb : bv_scope.
Infix "#" := bv_zero_extend (at level 65) : bv_scope.
Infix "||" := (bv_concat _) : bv_scope.

Notation "x ?" := (bv_odd x) : bv_scope.

Section definitions.
  Record Registers :=
    mkRegisters { r_A : bv 8 ; r_B : bv 4 ; r_cnt : bv 2 ; r_busy : bv 1}.

  Definition Registers0 := mkRegisters 0 0 0 0.

  Record In :=
    mkIn { in_A : bv 4 ; in_B : bv 4 ; in_valid : bv 1}.

  Definition In0 := mkIn 0 0 0.

  Record Out :=
    mkOut { out_P : bv 8 ; out_ready : bv 1 }.

  Definition Out0 := mkOut 0 0.

  Record ILeakage :=
    mkILeak { leak_valid : bv 1 ; leak_ready : bv 1}.

  Record State :=
    mkState { R : Registers; T : list ILeakage; Y : list Out }.

  Definition State0 := mkState Registers0 [] [].

  (* One shift-and-add step: conditionally add `b` into the high half of `a` then
   shift-right by one by reassembly. *)
  Definition shift_and_add (b : bv 4) (a : bv 8) : bv 8 :=
    let t0 := bv_extract 4 5 a in
    let t1 := if a? then 5#b else 0 in
    t0 + t1 || bv_extract 1 3 a.

  Definition cycle (s : State) (x : In) : State :=
    if s.(R).(r_busy) =? 0
    then
      if x.(in_valid) =? 1
      then
        let ra' := 8#x.(in_A) in
        let rb' := x.(in_B) in
        let rcount' := 3 in
        let rbusy' := 1 in
        let r' := mkRegisters ra' rb' rcount' rbusy' in
        let t' := s.(T) ++ [mkILeak x.(in_valid) 0 ] in
        let y' := s.(Y) ++ [Out0] in
        {| R := r'; T := t'; Y := y' |}
      else
        let t' := s.(T) ++ [mkILeak x.(in_valid) 0 ] in
        let r' := s.(R) in
        let s' := mkState r' t' in
        let y' := s.(Y) ++ [Out0] in
        {| R := r'; T := t'; Y := y' |}
    else
      let ra' := shift_and_add s.(R).(r_B) s.(R).(r_A) in
      let rb' := s.(R).(r_B) in
      if s.(R).(r_cnt) =? 0
      then
        let rcount' := 0 in
        let rbusy' := 0 in
        let r' := mkRegisters ra' rb' rcount' rbusy' in
        let t' := s.(T) ++ [mkILeak x.(in_valid) 1 ] in
        let s' := mkState r' t' in
        let y' := s.(Y) ++ [mkOut ra' 1] in
        {| R := r'; T := t'; Y := y' |}
      else
        let rcount' := s.(R).(r_cnt) - 1 in
        let rbusy' := 1 in
        let r' := mkRegisters ra' rb' rcount' rbusy' in
        let t' := s.(T) ++ [mkILeak x.(in_valid) 0 ] in
        let s' := mkState r' t' in
        let y' := s.(Y) ++ [Out0] in
        {| R := r'; T := t'; Y := y' |}.

  Definition cycles s xs := fold_left cycle xs s.
End definitions.

Section functional.
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
    intros n a b. induction n; simplify.
    - unfold repeat_shift_and_add', repeat_shift_and_add. done.
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
      end; done.

  Lemma shift_and_add4'_multiplies : forall a b,
      (0 <= a < bv_modulus 4%N)%Z ->
      (0 <= b < bv_modulus 4%N)%Z ->
      shift_and_add4' b a = (a * b)%Z.
  Proof.
    intros a b Ha Hb. replace (bv_modulus 4%N) with 16%Z in * by easy. by_cases16.
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
    unfold bv_modulus in *; simplify. nia.
  Qed.

  Lemma bv_eqb_eq {n} : forall (x y : bv n), (x =? y) = true <-> x = y.
  Proof.
    intuition; simplify.
    - unfold bv_eqb in *. destruct (bv_eq_dec n x y); done.
    - unfold bv_eqb. destruct (bv_eq_dec n y y); easy.
  Qed.

  Lemma bv_eqb_neq {n} : forall (x y : bv n), (x =? y) = false <-> x <> y.
  Proof.
    intuition; simplify.
    - unfold bv_eqb in *. destruct (bv_eq_dec n y y); done.
    - unfold bv_eqb. destruct (bv_eq_dec n x y); done.
  Qed.

  Lemma bv_not_zero_one : forall (x : bv 1), x <> 0 <-> x = 1.
  Proof.
    simplify.
    assert (x = 0 \/ x = 1).
    { apply bv_1_ind with (P := (fun x => x = 0 \/ x = 1)); equality. }
    split; simplify.
    - destruct_or!; done.
    - destruct_or!; done.
  Qed.

  Lemma bv_not_one_zero : forall (x : bv 1), x <> 1 <-> x = 0.
  Proof.
    simplify.
    assert (x = 0 \/ x = 1).
    { apply bv_1_ind with (P := (fun x => x = 0 \/ x = 1)); equality. }
    split; simplify.
    - destruct_or!; done.
    - destruct_or!; done.
  Qed.

  Definition busy (s : State) := s.(R).(r_busy) <> 0.
  Definition finished (s : State) := s.(R).(r_cnt) = 0.
  Definition valid (x : In) := x.(in_valid) = 1.

  Definition cycle_idle_valid s1 x s2 : Prop :=
    ~ busy s1 -> valid x -> s2 = cycle s1 x ->
    s2 = s1 <| R := {| r_A := 8#x.(in_A); r_B := x.(in_B); r_cnt := 3; r_busy := 1 |} |>
            <| T := s1.(T) ++ [{| leak_valid := 1; leak_ready := 0 |}] |>
            <| Y := s1.(Y) ++ [Out0] |>.

  Lemma cycle_idle_valid_holds : forall s1 x s2, cycle_idle_valid s1 x s2.
  Proof.
    unfold cycle_idle_valid. simplify.
    unfold cycle in *. unfold busy in *.
    unfold valid in *. rewrite <- bv_eqb_neq in H.
    Search (_ <> false). apply not_false_is_true in H.
    rewrite H0. rewrite H. simplify. done.
  Qed.

  Definition cycle_idle_invalid s1 x s2 : Prop :=
    ~ busy s1 -> ~ valid x -> s2 = cycle s1 x ->
    s2 = s1 <| T := s1.(T) ++ [{| leak_valid := 0; leak_ready := 0 |}] |>
            <| Y := s1.(Y) ++ [Out0] |>.

  Lemma cycle_idle_invalid_holds : forall s1 x s2, cycle_idle_invalid s1 x s2.
  Proof.
    unfold cycle_idle_invalid. simplify.
    unfold cycle, busy, valid in *.
    rewrite <- bv_eqb_neq in H. apply not_false_is_true in H.
    rewrite H. rewrite bv_not_one_zero in H0.
    rewrite H0. simplify. done.
  Qed.

  Definition cycle_busy_unfinished s1 x s2 : Prop :=
    busy s1 -> ~ finished s1 -> s2 = cycle s1 x ->
    s2 = s1 <| R; r_A := shift_and_add s1.(R).(r_B) s1.(R).(r_A) |>
            <| R; r_cnt := s1.(R).(r_cnt) - 1 |>
            <| T := s1.(T) ++ [{| leak_valid := x.(in_valid); leak_ready := 0 |}] |>
            <| Y := s1.(Y) ++ [Out0] |> .

  Lemma cycle_busy_unfinished_holds : forall s1 x s2, cycle_busy_unfinished s1 x s2.
  Proof.
    unfold cycle_busy_unfinished. simplify.
    unfold cycle, busy, finished in *.
    rewrite bv_not_zero_one in H. rewrite H.
    simplify. rewrite <- bv_eqb_neq in H0. rewrite H0.
    done.
  Qed.

  Definition cycle_busy_finished s1 x s2 : Prop :=
    busy s1 -> finished s1 -> s2 = cycle s1 x ->
    s2 = s1 <| R; r_A := shift_and_add s1.(R).(r_B) s1.(R).(r_A) |>
            <| R; r_cnt := 0 |>
            <| R; r_busy := 0 |>
            <| T := s1.(T) ++ [{| leak_valid := x.(in_valid); leak_ready := 1 |}] |>
            <| Y := s1.(Y) ++ [{|
                             out_P := shift_and_add s1.(R).(r_B) s1.(R).(r_A);
                             out_ready := 1
                           |}]
              |>.

  Lemma cycle_busy_finished_holds : forall s1 x s2, cycle_busy_finished s1 x s2.
  Proof.
    unfold cycle_busy_finished. simplify.
    unfold cycle, busy, finished in *.
    rewrite H0. rewrite bv_not_zero_one in H.
    rewrite H. simplify. done.
  Qed.

  Ltac unroll_cycle_predicates :=
    unfold cycle_idle_valid, cycle_idle_invalid, cycle_busy_unfinished,
      cycle_busy_finished, busy, finished, valid in *.

  Ltac cycles_correct_auto :=
    unroll_cycle_predicates; simplify;
      solve
        [ intuition
        | bv_solve ].

  Ltac unroll_nested_cycle :=
    match goal with
    | _ : context[cycle (cycle ?s ?x) _] |- _ =>
        let s' := fresh "s" in
        remember (cycle s x) as s'
    | |- context[cycle ?s ?x] =>
        let s' := fresh "s" in
        remember (cycle s x) as s'
    end.

  Tactic Notation "unroll_nested_cycle!" := repeat progress unroll_nested_cycle.

  (* Finally, with all those helper theorems out of the way, we can now prove
     the following correctness property:

     For any cycle where the circuit is idle, if a valid [a] and [b] are
     provided, four cycles later it will produce [a *| b]. *)
  Theorem cycles_correct : forall s s' x1 x2 x3 x4 x5 a b,
      ~ busy s -> x1 = {| in_A := a; in_B := b; in_valid := 1 |} ->
      s' = cycles s [x1; x2; x3; x4; x5] ->
      s'.(Y) = s.(Y) ++ [Out0; Out0; Out0; Out0; {| out_P := a *| b; out_ready := 1 |}].
  Proof.
    intros. simpl in H1. unroll_nested_cycle!. rewrite H0 in Heqs3.
    apply cycle_idle_valid_holds      in Heqs3; try cycles_correct_auto.
    apply cycle_busy_unfinished_holds in Heqs2; try cycles_correct_auto.
    apply cycle_busy_unfinished_holds in Heqs1; try cycles_correct_auto.
    apply cycle_busy_unfinished_holds in Heqs0; try cycles_correct_auto.
    apply cycle_busy_finished_holds   in H1   ; try cycles_correct_auto.
    simplify. repeat rewrite <- app_assoc. repeat progress f_equal.
    apply shift_and_add4_correct.
  Admitted.
End functional.

Section ct.
  Definition SLeakage := option (bv 4).

  Definition public1 x := if x.(in_valid) =? 1 then Some x.(in_A) else None.

  Definition public := map public1.

  Definition PredictorState := option nat.

  Definition predictor_step (st : PredictorState) (s : SLeakage) :=
    match st with
    | Some (S n) => Some n
    | Some O => None
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
    | Some O =>
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

  Section ex.
    Let xs := [mkIn 3 4 1; In0; In0; In0; In0; In0].

    Compute (cycles State0 xs, predict (public xs)).
  End ex.

  Definition rep (x : State) (y : PredictorState) : Prop :=
    (exists v, y = Some v /\
            bv_unsigned x.(R).(r_cnt) = (Z.of_nat v) /\
            (v <= 3)%nat /\
            x.(R).(r_busy) = 1
    )
    \/ (y = None /\ x.(R).(r_busy) = 0).

  Lemma bv_not_zero_nat_succ {l} : forall (b : bv l) n,
      bv_unsigned b = Z.of_nat (S n) -> b <> (bv_0 l).
  Proof.
    simplify. intuition. rewrite bv_eq in H0.
    rewrite H in H0. Search bv_unsigned.
    rewrite bv_0_unsigned in H0. lia.
  Qed.

  Lemma simulation_step : forall s1 s2 s1' s2' x,
      rep s1 s2 ->
      s1' = cycle s1 x ->
      s2' = predictor_step s2 (public1 x) ->
      rep s1' s2'.
  Proof.
    unfold rep, cycle, predictor_step, public1.
    simplify. inv H.
    - inv H0 as [v]. inv H. inv H1. inv H0. destruct v as [| v'].
      + assert (s1.(R).(r_cnt) = 0) by bv_solve.
        right. rewrite H0. rewrite H2. done.
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
    s1' = cycles s1 xs ->
    s2' = predictor_steps s2 (public xs) ->
    rep s1' s2'.
  Proof.
    induction xs as [| y ys IHy ]; simplify; try equality.
    - assert (rep (cycle s1 y) (predictor_step s2 (public1 y))).
      { apply simulation_step with (s1 := s1) (s2 := s2) (x := y); eauto. }
      unfold cycles, predictor_steps. eapply IHy.
      apply H0. equality. equality.
  Qed.

  Definition leak_next (s : State) (x : In) :=
    let valid := x.(in_valid) in
    let ready :=
      if s.(R).(r_busy) =? 1
      then
        if s.(R).(r_cnt) =? 0
        then 1
        else 0
      else 0
    in
    {| leak_valid := valid; leak_ready := ready |}.

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

  Lemma cycles_app' : forall xs x s1 s2 s3,
      s2 = cycles s1 xs ->
      s3 = cycles s1 (xs ++ [x]) ->
      s3.(T) = s2.(T) ++ [leak_next s2 x].
  Proof.
    induction xs as [| z zs IHz ]; simplify.
    - unfold cycle, leak_next. repeat case_match; try equality.
      + rewrite bv_eqb_eq in H1. rewrite bv_eqb_eq in H.
        rewrite H in H1. inv H1.
      + rewrite bv_eqb_eq in H1. rewrite bv_eqb_eq in H.
        rewrite H in H1. inv H1.
      + rewrite bv_eqb_neq in H1. rewrite bv_eqb_neq in H.
        apply bv_not_zero_one in H. contradiction.
    - apply IHz with (s1 := (cycle s1 z)); equality.
  Qed.

  Lemma cycles_app : forall xs x,
      T (cycles State0 (xs ++ [x])) =
        T (cycles State0 xs) ++ [leak_next (cycles State0 xs) x].
  Proof.
    simplify. apply cycles_app' with (xs := xs) (s1 := State0); equality.
  Qed.

  Theorem cycles_ct : exists f, forall xs s,
      s = cycles State0 xs -> s.(T) = f (public xs).
  Proof.
    exists predict.
    induction xs as [| z zs IHz ] using rev_ind; simplify.
    - equality.
    - rewrite cycles_app. unfold public. rewrite map_app.
      simplify. rewrite predict_app. rewrite IHz by equality.
      unfold public. repeat f_equal. apply simulation_predict_leak.
      apply simulation_many_step with (xs := zs) (s1 := State0) (s2 := None).
      + apply simulation_initial.
      + equality.
      + equality.
  Qed.
End ct.
