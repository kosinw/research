(**********************************************************************************)
(*                                                                                *)
(*             multiplier2.v - Shift-and-add 4-bit multiplier.                    *)
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
(*  We prove a similiar proof to [multiplier1] except that the circuit has a      *)
(*  short circuiting mechanism that allows it to end computation early.           *)
(*  This corresponds to having a more sophisticated predictor function.           *)
(*                                                                                *)
(**********************************************************************************)

From research Require Import base bitvector.
From stdpp Require Import option.

Local Open Scope bv_scope.

Section circuit.
  Record Registers :=
    { a : bv 4
    ; b : bv 4
    ; c : bv 2
    ; p : bv 8
    ; busy : bool
    }.

  Record _I :=
    { in_a : bv 4
    ; in_b : bv 4
    }.

  Definition I := option _I.

  Record _O :=
    { out_p : bv 8
    }.

  Definition O := option _O.

  Record ILeakage :=
    { leak_valid : bool
    ; leak_ready : bool
    }.

  Record State :=
    { R : Registers
    ; T : list ILeakage
    ; Y : list O
    }.

  Definition State0 :=
    {|
      R := {| a := 0; b := 0; c := 0; p := 0; busy := false |};
      T := [];
      Y := []
    |}.

  Definition shift_and_add (R : Registers) : Registers :=
    match R.(a) =? 0 with
    | true => R
    | false =>
        let p' : bv 8 :=
          let t := if R.(a)? then 8#R.(b) else 0 in
          R.(p) + (t ≪ (8#R.(c)))
        in
        let a' := R.(a) ≫ 1 in
        let c' := R.(c) + 1 in
        R <| a := a' |> <| p := p' |> <| c := c' |>
    end.

  Definition circuit_step (s : State) (x : I) : State :=
    match s.(R).(busy) with
    | false =>
        match x with
        | Some x =>
            let R' := {| a := x.(in_a); b := x.(in_b); c := 0; p := 0; busy := true |} in
            let T' := s.(T) ++ [{| leak_valid := true; leak_ready := false |}] in
            let Y' := s.(Y) ++ [None] in
            s <| R := R' |> <| T := T' |> <| Y := Y' |>
        | None =>
            let T' := s.(T) ++ [{| leak_valid := false; leak_ready := false |}] in
            let Y' := s.(Y) ++ [None] in
            s <| T := T' |> <| Y := Y' |>
        end
    | true =>
        let leak_valid' := match x with Some _ => true | _ => false end in
        match s.(R).(a) =? 0 with
        | true =>
            let R' := s.(R) <| busy := false |> in
            let T' := s.(T) ++ [{| leak_valid := leak_valid'; leak_ready := true |}] in
            let Y' := s.(Y) ++ [Some {| out_p := s.(R).(p) |}] in
            s <| R := R' |> <| T := T' |> <| Y := Y' |>
        | false =>
            let R' := shift_and_add s.(R) in
            let T' := s.(T) ++ [{| leak_valid := leak_valid'; leak_ready := false |}] in
            let Y' := s.(Y) ++ [None] in
            s <| R := R' |> <| T := T' |> <| Y := Y' |>
        end
    end.

  Definition circuit_steps s xs := fold_left circuit_step xs s.
End circuit.

Section ct.
  Record _SLeakage := { leak_a : bv 4 }.
  Definition SLeakage := option _SLeakage.

  Definition public1 : I -> SLeakage :=
    option_map (fun x => {| leak_a := x.(in_a) |}).

  Definition public := map public1.

  Definition PredictorState := option (bv 4).

  Definition predictor_step (st : PredictorState) (s : SLeakage) :=
    match st with
    | Some x =>
        match x =? 0 with
        | true => None
        | false => Some (x ≫ 1)
        end
    | None =>
        match s with
        | Some {| leak_a := x |} => Some x
        | None   => None
        end
    end.

  Definition predictor_steps (st : PredictorState) (xs : list SLeakage) :=
    fold_left predictor_step xs st.

  Definition predict_next (st : PredictorState) (s : SLeakage) :=
    match st with
    | Some x =>
        let leak_valid' := match s with Some _ => true | None => false end in
        let leak_ready' := x =? 0 in
        {| leak_valid := leak_valid'; leak_ready := leak_ready' |}
    | None =>
        match s with
        | Some _ => {| leak_valid := true; leak_ready := false |}
        | None => {| leak_valid := false; leak_ready := false |}
        end
    end.

  Fixpoint predict' st xs :=
    match xs with
    | [] => []
    | x :: xs' => predict_next st x :: predict' (predictor_step st x) xs'
    end.

  Definition predict xs := predict' None xs.

  Definition rep (x : State) (y : PredictorState) : Prop :=
    (exists v, y = Some v /\ x.(R).(a) = v /\ x.(R).(busy) = true)
    \/ (y = None /\ x.(R).(busy) = false).

  Infix "`R`" := rep (at level 70).

  Lemma simulation_step : forall s1 s2 s1' s2' x,
      s1 `R` s2 ->
      s1' = circuit_step s1 x ->
      s2' = predictor_step s2 (public1 x) ->
      s1' `R` s2'.
  Proof.
    unfold rep, circuit_step, predictor_step, public1, option_map.
    simplify. inv H.
    - inv H0 as [v]. propositional. rewrite H2. simplify.
      destruct (s1.(R).(a) =? 0) eqn:Heqn; simplify.
      + eauto.
      + left. exists (s1.(R).(a) ≫ 1). propositional.
        * unfold shift_and_add. rewrite Heqn. simplify.
          equality.
        * unfold shift_and_add. rewrite Heqn. simplify.
          equality.
    - inv H0. rewrite H1. simplify. destruct x as [x'|]; simplify.
      + left. exists (x'.(in_a)). equality.
      + right. equality.
  Qed.

  Lemma simulation_initial : State0 `R` None.
  Proof. unfold rep; equality. Qed.

  Lemma simulation_many_step : forall xs s1 s2 s1' s2',
    s1 `R` s2 ->
    s1' = circuit_steps s1 xs ->
    s2' = predictor_steps s2 (public xs) ->
    s1' `R` s2'.
  Proof.
    induction xs as [| y ys IHy ]; simplify; try equality.
    - assert (rep (circuit_step s1 y) (predictor_step s2 (public1 y))).
      { apply simulation_step with (s1 := s1) (s2 := s2) (x := y); eauto. }
      unfold circuit_steps, predictor_steps. eapply IHy; eauto.
  Qed.

  Definition leak_next (s : State) (x : I) :=
    match s with
    | {| R := {| a := a; busy := true |} |} =>
        let leak_valid' := match x with Some _ => true | None => false end in
        let leak_ready' := a =? 0 in
        {| leak_valid := leak_valid'; leak_ready := leak_ready' |}
    | {| R := {| busy := false |} |} =>
        match x with
        | Some _ => {| leak_valid := true; leak_ready := false |}
        | None => {| leak_valid := false; leak_ready := false |}
        end
    end.

  Lemma simulation_predict_leak : forall s1 s2 x,
      s1 `R` s2 -> leak_next s1 x = predict_next s2 (public1 x).
  Proof.
    unfold rep, leak_next, predict_next, public1.
    simplify. inv H.
    - firstorder; simplify. destruct s1; simplify.
      destruct R0; simplify. unfold option_map; simplify.
      destruct x; eauto.
    - propositional; simplify. destruct s1; simplify.
      destruct R0; simplify. unfold option_map; simplify.
      destruct x; eauto.
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
