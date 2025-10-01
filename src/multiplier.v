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

(**********************************************************************************)

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
  mkState { R : Registers ; T : list ILeakage}.

Definition State0 := mkState Registers0 [].

(* One shift-and-add step: conditionally add `b` into the high half of `a` then
   shift-right by one by reassembly. *)
Definition shift_and_add (b : bv 4) (a : bv 8) : bv 8 :=
  let t0 := bv_extract 4 5 a in
  let t1 := if a? then 5#b else 0 in
  t0 + t1 || bv_extract 1 3 a.

Definition cycle (s : State) (x : In) : State * Out :=
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
      let s' := mkState r' t' in
      (s', Out0)
    else
      let t' := s.(T) ++ [mkILeak x.(in_valid) 0 ] in
      let r' := s.(R) in
      let s' := mkState r' t' in
      (s', Out0)
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
      let o' := mkOut ra' 1 in
      (s', o')
    else
      let rcount' := s.(R).(r_cnt) - 1 in
      let rbusy' := 1 in
      let r' := mkRegisters ra' rb' rcount' rbusy' in
      let t' := s.(T) ++ [mkILeak x.(in_valid) 0 ] in
      let s' := mkState r' t' in
      (s', Out0).

Section functional.
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

  Definition cycle_idle_valid s1 x s2 y : Prop :=
    ~ busy s1 -> valid x -> (s2, y) = cycle s1 x ->
    (s2, y) = (s1 <| R := {| r_A := 8#x.(in_A); r_B := x.(in_B); r_cnt := 3; r_busy := 1 |} |>
                  <| T := s1.(T) ++ [{| leak_valid := 1; leak_ready := 0 |}] |>,
               Out0).

  Lemma cycle_idle_valid_holds : forall s1 x s2 y, cycle_idle_valid s1 x s2 y.
  Proof.
    unfold cycle_idle_valid. simplify.
    unfold cycle in *. unfold busy in *.
    unfold valid in *. rewrite <- bv_eqb_neq in H.
    Search (_ <> false). apply not_false_is_true in H.
    rewrite H in H1. rewrite H0 in H1. simplify. done.
  Qed.

  Definition cycle_idle_invalid s1 x s2 y : Prop :=
    ~ busy s1 -> ~ valid x -> (s2, y) = cycle s1 x ->
    (s2, y) = (s1 <| T := s1.(T) ++ [{| leak_valid := 0; leak_ready := 0 |}] |>,
               Out0).

  Lemma cycle_idle_invalid_holds : forall s1 x s2 y, cycle_idle_invalid s1 x s2 y.
  Proof.
    unfold cycle_idle_invalid. simplify.
    unfold cycle, busy, valid in *.
    rewrite <- bv_eqb_neq in H. apply not_false_is_true in H.
    rewrite H in H1. rewrite bv_not_one_zero in H0.
    rewrite H0 in H1; simplify. done.
  Qed.

  Definition cycle_busy_unfinished s1 x s2 y : Prop :=
    busy s1 -> ~ finished s1 -> (s2, y) = cycle s1 x ->
    (s2, y) = (s1 <| R; r_A := shift_and_add s1.(R).(r_B) s1.(R).(r_A) |>
                  <| R; r_cnt := s1.(R).(r_cnt) - 1 |>
                  <| T := s1.(T) ++ [{| leak_valid := x.(in_valid); leak_ready := 0 |}] |>,
               Out0).

  Lemma cycle_busy_unfinished_holds : forall s1 x s2 y, cycle_busy_unfinished s1 x s2 y.
  Proof.
    unfold cycle_busy_unfinished. simplify.
    unfold cycle, busy, finished in *.
    rewrite bv_not_zero_one in H. rewrite H in H1.
    simplify. rewrite <- bv_eqb_neq in H0. rewrite H0 in H1.
    rewrite H. done.
  Qed.

  Definition cycle_busy_finished s1 x s2 y : Prop :=
    busy s1 -> finished s1 -> (s2, y) = cycle s1 x ->
    (s2, y) = (s1 <| R; r_A := shift_and_add s1.(R).(r_B) s1.(R).(r_A) |>
                  <| R; r_cnt := 0 |>
                  <| R; r_busy := 0 |>
                  <| T := s1.(T) ++ [{| leak_valid := x.(in_valid); leak_ready := 1 |}] |>,
                  {| out_P := s2.(R).(r_A); out_ready := 1 |}).

  Lemma cycle_busy_finished_holds : forall s1 x s2 y, cycle_busy_finished s1 x s2 y.
  Proof.
    unfold cycle_busy_finished. simplify.
    unfold cycle, busy, finished in *.
    rewrite H0 in H1. rewrite bv_not_zero_one in H.
    rewrite H in H1. simplify. inv H1. done.
  Qed.

  Ltac unroll_cycle_predicates :=
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

  Ltac cycles_correct_auto :=
    unfold_pairs; subst;
    try (unroll_cycle_predicates;
         solve
           [ intuition
           | simplify; bv_solve ]).

  (* Finally, with all those helper theorems out of the way, we can now prove
     the following correctness property:

     For any cycle where the circuit is idle, if a valid [a] and [b] are
     provided, four cycles later it will produce [a *| b]. *)
  Theorem cycles_correct : forall s s' x1 x2 x3 x4 x5 ys a b,
      ~ busy s -> x1 = {| in_A := a; in_B := b; in_valid := 1 |} ->
      (s', ys) = cycles s [x1; x2; x3; x4; x5] ->
      ys = [Out0; Out0; Out0; Out0; {| out_P := a *| b; out_ready := 1 |}].
  Proof.
    simplify. unroll_lets.
    apply cycle_idle_valid_holds      in Hlet0; cycles_correct_auto.
    apply cycle_busy_unfinished_holds in Hlet1; cycles_correct_auto.
    apply cycle_busy_unfinished_holds in Hlet2; cycles_correct_auto.
    apply cycle_busy_unfinished_holds in Hlet3; cycles_correct_auto.
    apply cycle_busy_finished_holds   in Hlet4; cycles_correct_auto.
    simplify. repeat f_equal. by apply shift_and_add4_correct.
  Qed.
End functional.

(* NOTE knwabueze for aerbsen: I think we talked about using this definition for
   the extraction from the list of inputs to the specification leakage.

   {[ Definition SLeakage := bv 4.

      Definition extract : list In -> list SLeakage :=
        flat_map (fun i => if i.(in_valid) =? 1 then [i.(in_A)] else []). ]}

   However, I think this original definition is problematic. The predictor
   function would need to know whether or not a value for [A] was provided on
   each cycle, not just the total list of provided values. *)

Section ct.
  Definition cycle' s x :=
    fst (cycle s x).

  Definition cycles' s xs :=
    fold_left cycle' xs s.

  Definition SLeakage := option (bv 4).

  Definition extract1 x :=
    if x.(in_valid) =? 1 then Some x.(in_A) else None.

  Definition extract :=
    map extract1.

  Record PredictorState :=
    mkPredictorState { ps_count : option nat ; ps_valid : bool }.

  Definition PredictorState0 := mkPredictorState None false.

  Definition predictor_step (st : PredictorState) (s : SLeakage) :=
    match st with
    | {| ps_count := Some (S n) |} =>
        match s with
        | Some _ => {| ps_count := Some n; ps_valid := true |}
        | None   => {| ps_count := Some n; ps_valid := false |}
        end
    | {| ps_count := Some O |} =>
        match s with
        | Some _ => {| ps_count := None; ps_valid := true |}
        | None   => {| ps_count := None; ps_valid := false |}
        end
    | {| ps_count := None |} =>
        match s with
        | Some _ => {| ps_count := Some 4%nat; ps_valid := true |}
        | None   => {| ps_count := None; ps_valid := false |}
        end
    end.

  Definition predictor_steps st ss :=
    fold_left predictor_step ss st.

  Definition predict_next prefix :=
    match predictor_steps PredictorState0 prefix with
    | {| ps_count := Some (S _); ps_valid := v |} =>
        {| leak_valid := if v then 1 else 0; leak_ready := 0 |}
    | {| ps_count := Some O; ps_valid := v |} =>
        {| leak_valid := if v then 1 else 0; leak_ready := 1 |}
    | {| ps_count := None; ps_valid := v |} =>
        {| leak_valid := if v then 1 else 0; leak_ready := 0 |}
    end.

  Fixpoint predict' prefix xs :=
    match xs with
    | [] => []
    | x :: xs' => predict_next (prefix ++ [x]) :: predict' (prefix ++ [x]) xs'
    end.

  Definition predict xs := predict' [] xs.

  Lemma predict_app' : forall ys y t t' p,
      t = predict' p ys ->
      t' = predict' p (ys ++ [y]) ->
      t' = t ++ [predict_next (p ++ ys ++ [y])].
  Proof.
    induction ys as [| y' ys']; simplify.
    - done.
    - f_equal.
      replace (p ++ y' :: ys' ++ [y]) with (p ++ [y'] ++ ys' ++ [y]); cycle 1.
      { Search (_ ++ _ :: _ = _ ++ [_] ++ _). rewrite <- cons_middle. done. }
      specialize (IHys' y
                    (predict' (p ++ [y']) ys')
                    (predict' (p ++ [y']) (ys' ++ [y]))
                    (p ++ [y'])).
      rewrite app_assoc. apply IHys'; done.
  Qed.

  Lemma predict_app : forall ys y,
      predict (ys ++ [y]) = predict ys ++ [predict_next (ys ++ [y])].
  Proof.
    unfold predict; intros.
    Search ([] ++ _ = _).
    replace ys with ([] ++ ys) by apply app_nil_l.
    rewrite <- app_assoc.
    apply predict_app'; done.
  Qed.

  Definition next_ileak (s : State) (x : In) :=
    if s.(R).(r_busy) =? 0
    then {| leak_valid := x.(in_valid); leak_ready := 0 |}
    else
      if s.(R).(r_cnt) =? 0
      then {| leak_valid := x.(in_valid); leak_ready := 1  |}
      else {| leak_valid := x.(in_valid); leak_ready := 0 |}.

  Lemma cycles_app : forall xs x s1 s2 s3,
      s2 = cycles' s1 xs ->
      s3 = cycles' s1 (xs ++ [x]) ->
      s3.(T) = s2.(T) ++ [next_ileak s2 x].
  Proof.
    induction xs as [| y ys IHys ]; intros.
    - simplify. unfold cycle'.
      unfold cycle, next_ileak.
      repeat case_match; equality.
    - apply IHys with (s1 := (cycle' s1 y)); equality.
  Qed.

  Lemma destruct_snoc {A} : forall (xs : list A),
      xs = [] \/ (exists ys y, xs = ys ++ [y]).
  Proof.
    intros xs. apply rev_ind with (l := xs); simplify.
    - left. equality.
    - right. exists l. exists x. equality.
  Qed.

  Lemma predict_next_correct' : forall xs1 xs2 x ys s,
      ys = extract (xs1 ++ xs2 ++ [x]) ->
      s = cycles' State0 (xs1 ++ xs2) ->
      next_ileak s x = predict_next ys.
  Proof.
    intros xs1. apply rev_ind with (l := xs1).
    - intros xs2. apply rev_ind with (l := xs2); simplify.
      + unfold next_ileak, predict_next, extract1; simplify.
        repeat case_match; try equality.
        * inv H. rewrite bv_eqb_eq in H1.
          rewrite H1. equality.
        * inv H. rewrite bv_eqb_neq in H1.
          rewrite bv_not_one_zero in H1.
          rewrite H1. equality.
      + admit.
    - simplify. destruct (destruct_snoc xs2); subst.
      + repeat rewrite <- app_assoc.
        replace (l ++ [x] ++ [] ++ [x0])
          with ((l ++ [x] ++ []) ++ [x0]); cycle 1.
        { simplify. rewrite <- app_assoc. equality. }
        replace ([x] ++ []) with ([] ++ [x]) by equality.
        rewrite <- app_assoc.
        replace ([] ++ [x]) with ([x]) by equality.
        apply H with (xs2 := [x]); equality.
      + inv H0. inv H1.
        replace ((l ++ [x]) ++ x1 ++ [x2])
          with (l ++ ([x] ++ x1 ++ [x2])); cycle 1.
        { simplify. rewrite <- app_assoc. equality. }
        replace ((l ++ [x]) ++ (x1 ++ [x2]) ++ [x0])
          with (l ++ ([x] ++ x1 ++ [x2]) ++ [x0]); cycle 1.
        { simplify. repeat rewrite <- app_assoc. equality. }
        apply H with (xs2 := ([x] ++ x1 ++ [x2])); equality.
  Admitted.

  Lemma predict_next_correct : forall xs x ys s,
      ys = extract (xs ++ [x]) ->
      s = cycles' State0 xs ->
      next_ileak s x = predict_next ys.
  Proof.
    simplify. apply predict_next_correct' with (xs1 := xs) (xs2 := []).
    equality. rewrite app_nil_r. equality.
  Qed.

  Theorem cycles_ct : exists f, forall xs ys s,
      ys = extract xs ->
      s = cycles' State0 xs ->
      s.(T) = f ys.
  Proof.
    unfold extract. exists predict. intros xs.
    apply rev_ind with (l := xs); simplify.
    - equality.
    - Search (map _ (_ ++ _)). rewrite map_app.
      simplify. rewrite predict_app.
      rewrite cycles_app with (x := x) (xs := l)
             (s1 := State0)
             (s2 := (cycles' State0 l))
        by equality.
      rewrite <- H with (s := (cycles' State0 l)) by equality.
      repeat f_equal. fold extract.
      replace (extract l ++ [extract1 x]) with (extract (l ++ [x])) at 1
        by (unfold extract; rewrite map_app; equality).
      apply predict_next_correct with (xs := l); equality.
  Qed.
End ct.
