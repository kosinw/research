(**********************************************************************************)
(*                                                                                *)
(*  multiplier.v - Shift-and-add 4-bit multiplier.                                *)
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
(*  hyperproperty. The statement of the property looks as follows (which we state *)
(*  as an equivalent single-copy trace property):                                 *)
(*                                                                                *)
(*  There exists some predictor [f] such that given a cycle schedule [C],         *)
(*  starting from a reset state, the multiplier circuit [M] will produce an       *)
(*  implementation leakage trace [t'].                                            *)
(*                                                                                *)
(*  A specification leakage trace [t] is extracted from schedule [C] which        *)
(*  will record the values of [A] and [valid] each cycle. On termination,         *)
(*                                                                                *)
(*                              [t' = f(t)].                                      *)
(*                                                                                *)
(**********************************************************************************)

From stdpp Require Import base tactics bitvector.
From RecordUpdate Require Import RecordUpdate.

Local Open Scope bv_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Ltac simplify := repeat progress (intros; csimpl in *; subst).

Definition make_visible {X} (f : X) := f.

Notation "` f" := (make_visible f) (at level 10, format "` f").

Tactic Notation "unfold" "notation" constr(f) := change f with (`f).
Tactic Notation "fold" "notation" constr(f) := unfold make_visible.

Definition bv_eqb {n} (x y : bv n) : bool :=
  Eval cbv beta iota zeta delta [ bool_decide decide_rel ] in
    bool_decide (x = y).

Definition bv_odd {n} (x : bv n) := Z.odd (bv_unsigned x).

Infix "=?" := bv_eqb : bv_scope.
Infix "#" := bv_zero_extend (at level 65) : bv_scope.
Infix "||" := (bv_concat _) : bv_scope.

Notation "x ?" := (bv_odd x) : bv_scope.

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

Fixpoint cycles (s : State) (xs : list In) : State * list Out :=
  match xs with
  | [] => (s, [])
  | x :: xs' =>
      let (s', y) := cycle s x in
      let (s'', ys) := cycles s' xs' in
      (s'', y :: ys)
  end.

Fixpoint cycles' (s : State) (xs : list In) : State :=
  match xs with
  | [] => s
  | x :: xs' => cycles' (fst (cycle s x)) xs'
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

Lemma bv1_is_0_or_1 : forall (b : bv 1), b = 0 \/ b = 1.
Proof.
  intro b. Search "bv" "ind".
  apply bv_1_ind with (P := (fun b => b = 0 \/ b = 1)); intuition congruence.
Qed.

Definition busy (s : State) := s.(R).(r_busy) = 1.
Definition finished (s : State) := s.(R).(r_cnt) = 0.
Definition valid (x : In) := x.(in_valid) = 1.

Hint Extern 1 (_ = _ :> bv 1) =>
       match goal with
       | |- ?b = 0 :> bv 1 => pose proof (bv1_is_0_or_1 b); intuition
       | |- ?b = 1 :> bv 1 => pose proof (bv1_is_0_or_1 b); intuition
       end : multiplier.

Definition cycle_idle_valid s1 x s2 y : Prop :=
  ~ busy s1 -> valid x -> (s2, y) = cycle s1 x ->
  (s2, y) = (s1 <| R := {| r_A := 8#x.(in_A); r_B := x.(in_B); r_cnt := 3; r_busy := 1 |} |>
                <| T := s1.(T) ++ [{| leak_valid := 1; leak_ready := 0 |}] |>,
             Out0).

Lemma cycle_idle_valid_holds : forall s1 x s2 y, cycle_idle_valid s1 x s2 y.
Proof.
  unfold cycle_idle_valid. simplify.
  unfold cycle in *. unfold bv_eqb in *. unfold busy in *.
  unfold valid in *. assert (s1.(R).(r_busy) = 0) by auto with multiplier.
  repeat rewrite H2 in H1. simpl in *. rewrite H0 in H1.
  simplify. inv H1. done.
Qed.

Definition cycle_idle_invalid s1 x s2 y : Prop :=
  ~ busy s1 -> ~ valid x -> (s2, y) = cycle s1 x ->
  (s2, y) = (s1 <| T := s1.(T) ++ [{| leak_valid := 0; leak_ready := 0 |}] |>,
             Out0).

Lemma cycle_idle_invalid_holds : forall s1 x s2 y, cycle_idle_invalid s1 x s2 y.
Proof.
  unfold cycle_idle_invalid. simplify.
  unfold cycle, bv_eqb, busy, valid in *.
  assert (s1.(R).(r_busy) = 0) by auto with multiplier.
  assert (x.(in_valid) = 0) by auto with multiplier.
  rewrite H2, H3 in H1. simpl in *. inversion H1; clear H1.
  done.
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
  unfold cycle, bv_eqb, busy, finished in *.
  rewrite H in H1; simpl in *.
  destruct (bv_eq_dec 2 (r_cnt (R s1)) 0) as [Heq | Hneq].
  - done.
  - inv H1. intuition congruence.
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
  unfold cycle, bv_eqb, busy, finished in *.
  rewrite H in H1; simplify. rewrite H0 in H1.
  simplify. inversion H1; clear H1; subst. done.
Qed.

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

Ltac cycles_correct_auto :=
  unfold_pairs; subst; try (unfold_cycle_predicates; solve
                        [ intuition
                        | simplify; bv_solve ]).

(* Finally, with all those helper theorems out of the way, we can now prove the
   following correctness property:

   For any cycle where the circuit is idle, if a valid [a] and [b] are provided,
   four cycles later it will produce [a *| b]. *)
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

(* NOTE knwabueze for aerbsen: I think we talked about using this definition for
   the extraction from the list of inputs to the specification leakage.

   {[ Definition SLeakage := bv 4.

      Definition extract : list In -> list SLeakage := flat_map (fun i => if
        i.(in_valid) =? 1 then [i.(in_A)] else []). ]}

    However, I think this original definition is problematic. The predictor
    function would need to know whether or not a value for [A] was provided on
    each cycle, not just the total list of provided values. *)

Definition SLeakage := option (bv 4).

Definition extract : list In -> list SLeakage :=
  map (fun x => if x.(in_valid) =? 1 then Some x.(in_A) else None).

(* Predictor function which uses the prefix of the specification leakage trace
   to predict the next item in the implementation leakage trace. *)
Definition update_st (st : option nat * bool) (s : SLeakage) :=
  match st with
  | (Some (S n), _) =>
      match s with
      | Some _ => (Some n, true)
      | None => (Some n, false)
      end
  | (Some O, _) =>
      match s with
      | Some _ => (None, true)
      | None => (None, false)
      end
  | (None, _) =>
      match s with
      | Some _ => (Some 4%nat, true)
      | None => (None, false)
      end
  end.

Fixpoint predict_next' (prefix : list SLeakage) (st : option nat * bool) : ILeakage :=
  match prefix with
  | [] =>
      match st with
      | (None  , v) => {| leak_valid := bool_to_bv 1 v; leak_ready := 0 |}
      | (Some O, v) => {| leak_valid := bool_to_bv 1 v; leak_ready := 1 |}
      | (Some _, v) => {| leak_valid := bool_to_bv 1 v; leak_ready := 0 |}
      end
  | p :: ps => predict_next' ps (update_st st p)
  end.

Definition predict_next prefix := predict_next' prefix (None, false).

Fixpoint predict' prefix xs :=
  match xs with
  | [] => []
  | x :: xs' => predict_next (prefix ++ [x]) :: predict' (prefix ++ [x]) xs'
  end.

Definition predict xs := predict' [] xs.

(* First, we need a helper lemma that talks about one cycle's behavior on a the
   implementation leakage trace. This follows by doing cases analysis on the
   four fundamental outcomes that may happen on a cycle:

   1. The circuit is idle and recieves an invalid input.
   2. The circuit is idle and recieves a valid input.
   3. The circuit is busy, but r_cnt > 0.
   4. The circuit is busy, but r_cnt = 0. *)

Theorem cycles_ct : exists f, forall xs ys s,
    ys = extract xs ->
    s = cycles' State0 xs ->
    s.(T) = f ys.
Admitted.
