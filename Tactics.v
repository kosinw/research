From Stdlib Require Import Eqdep String NArith Arith Lia Program Bool.
From Stdlib Require Import List.
Export List ListNotations.

Ltac inductN n :=
  match goal with
  | [ |- forall x : ?E, _ ] =>
      match type of E with
      | Prop =>
          let H := fresh in intro H;
                            match n with
                            | 1 => dependent induction H
                            | S ?n' => inductN n'
                            end
      | _ => intro; inductN n
      end
  end.

Ltac same_structure x y :=
  match x with
  | ?f ?a1 ?b1 ?c1 ?d1 =>
      match y with
      | f ?a2 ?b2 ?c2 ?d2 =>
          same_structure a1 a2;
          same_structure b1 b2;
          same_structure c1 c2;
          same_structure d1 d2
      | _ => fail 2
      end
  | ?f ?a1 ?b1 ?c1 =>
      match y with
      | f ?a2 ?b2 ?c2 =>
          same_structure a1 a2;
          same_structure b1 b2;
          same_structure c1 c2
      | _ => fail 2
      end
  | ?f ?a1 ?b1 =>
      match y with
      | f ?a2 ?b2 => same_structure a1 a2; same_structure b1 b2
      | _ => fail 2
      end
  | ?f ?a1 =>
      match y with
      | f ?a2 => same_structure a1 a2
      | _ => fail 2
      end
  | _ =>
      match y with
      | ?f ?a1 ?b1 ?c1 ?d1 =>
          match x with
          | f ?a2 ?b2 ?c2 ?d2 =>
              same_structure a1 a2;
              same_structure b1 b2;
              same_structure c1 c2;
              same_structure d1 d2
          | _ => fail 2
          end
      | ?f ?a1 ?b1 ?c1 =>
          match x with
          | f ?a2 ?b2 ?c2 =>
              same_structure a1 a2;
              same_structure b1 b2;
              same_structure c1 c2
          | _ => fail 2
          end
      | ?f ?a1 ?b1 =>
          match x with
          | f ?a2 ?b2 => same_structure a1 a2; same_structure b1 b2
          | _ => fail 2
          end
      | ?f ?a1 =>
          match x with
          | f ?a2 => same_structure a1 a2
          | _ => fail 2
          end
      | _ => idtac
      end
  end.

Ltac instantiate_obvious1 H :=
  match type of H with
  | _ ++ _ = _ ++ _ -> _ => fail 1
  | ?x = ?y -> _ =>
      (same_structure x y; specialize (H eq_refl))
      || (has_evar (x, y); fail 3)
  | JMeq.JMeq ?x ?y -> _ =>
      (same_structure x y; specialize (H JMeq.JMeq_refl))
      || (has_evar (x, y); fail 3)
  | forall x : ?T, _ =>
      match type of T with
      | Prop => fail 1
      | _ =>
          let x' := fresh x in
          evar (x' : T);
          let x'' := eval unfold x' in x' in specialize (H x''); clear x';
                                       instantiate_obvious1 H
      end
  end.

Ltac instantiate_obvious H :=
  match type of H with
  | context[@eq string _  _] => idtac
  | _ => repeat instantiate_obvious1 H
  end.

Ltac instantiate_obviouses :=
  repeat match goal with
    | [ H : _ |- _ ] => instantiate_obvious H
    end.

Lemma indN: forall (P: N -> Prop),
    P 0%N ->
    (forall n: N, P n -> P (n + 1)%N) ->
    forall n, P n.
Proof. setoid_rewrite N.add_1_r. exact N.peano_ind. Qed.

Ltac induct e :=
  (induction e using indN || inductN e || dependent induction e); instantiate_obviouses.

Ltac invert' H := inversion H; clear H; subst.

Ltac invertN n :=
  match goal with
  | [ |- forall x : ?E, _ ] =>
      match type of E with
      | Prop =>
          let H := fresh in intro H;
                            match n with
                            | 1 => invert' H
                            | S ?n' => invertN n'
                            end
      | _ => intro; invertN n
      end
  end.

Ltac invert e := invertN e || invert' e.

Ltac invert0 e := invert e; fail.
Ltac invert1 e := invert0 e || (invert e; []).
Ltac invert2 e := invert1 e || (invert e; [|]).

Ltac simplify :=
  repeat match goal with
    | [ H : True |- _ ] => clear H
    end;
  repeat progress
    (simpl in *;
     intros;
     try autorewrite with core in *).

Ltac propositional := intuition idtac.

Ltac linear_arithmetic :=
  intros; repeat match goal with
            | [ |- context[max ?a ?b] ] =>
                let Heq := fresh "Heq" in destruct (Nat.max_spec a b) as [[? Heq] | [? Heq]];
                                          rewrite Heq in *; clear Heq
            | [ _ : context[max ?a ?b] |- _ ] =>
                let Heq := fresh "Heq" in destruct (Nat.max_spec a b) as [[? Heq] | [? Heq]];
                                          rewrite Heq in *; clear Heq
            | [ |- context[min ?a ?b] ] =>
                let Heq := fresh "Heq" in destruct (Nat.min_spec a b) as [[? Heq] | [? Heq]];
                                          rewrite Heq in *; clear Heq
            | [ _ : context[min ?a ?b] |- _ ] =>
                let Heq := fresh "Heq" in destruct (Nat.min_spec a b) as [[? Heq] | [? Heq]];
                                          rewrite Heq in *; clear Heq
            end; lia.

Ltac equality := intuition congruence.

Ltac cases E :=
  ((repeat match type of E with
      | _ \/ _ => destruct E as [E | E]
      end)
   || (match type of E with
      | N => destruct E using indN
      end)
   || (is_var E; destruct E)
   || match type of E with
     | {_} + {_} => destruct E
     | _ => let Heq := fresh "Heq" in destruct E eqn:Heq
     end);
  repeat match goal with
    | [ H : _ = left _ |- _ ] => clear H
    | [ H : _ = right _ |- _ ] => clear H
    end.
