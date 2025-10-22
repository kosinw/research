From research Require Import base program.

Record Circuit t m :=
  { run : m -> t -> t
  ; init : t
  }.

Definition refines
  `(c1 : Circuit t1 m1)
  `(c2 : Circuit t2 m2)
  (policy : m1 -> m2)
  (R : t1 -> t2 -> Prop) :=
  forall s1 s2,
    R s1 s2 ->
    (forall m s1' s2',
        s1' = c1.(run) m s1 ->
        s2' = c2.(run) (policy m) s2 ->
        R s1' s2').

Notation " c1 ⊑ c2" := (refines c1 c2 _ _) (at level 70).

Definition simulates `(c1 : Circuit t1 m1) `(c2 : Circuit t2 m2) (policy : m1 -> m2) :=
  exists R, R c1.(init) c2.(init) /\ refines c1 c2 policy R.

Notation "P ⊢ c1 ∼ c2" := (simulates c1 c2 P) (at level 60, c1 at next level).

Lemma refines_refl `(c : Circuit t m) : refines c c id eq.
Proof.
  cbv [refines]; simplify; equality.
Qed.

Lemma simulates_refl `(c : Circuit t m) : id ⊢ c ∼ c.
Proof.
  cbv [simulates]; exists eq; simplify; eauto using refines_refl.
Qed.

Lemma refines_trans `(c1 : Circuit t1 m1) `(c2 : Circuit t2 m2) `(c3 : Circuit t3 m3) :
  forall R1 R2 policy1 policy2,
    refines c1 c2 policy1 R1 ->
    refines c2 c3 policy2 R2 ->
    refines c1 c3 (policy2 ∘ policy1) (fun s1 s3 => exists s2, R1 s1 s2 /\ R2 s2 s3).
Proof.
  cbv [refines]. simplify. firstorder.
  eexists. firstorder.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma simulates_trans `(c1 : Circuit t1 m1) `(c2 : Circuit t2 m2) `(c3 : Circuit t3 m3) :
  forall policy1 policy2,
    policy1 ⊢ c1 ∼ c2 ->
    policy2 ⊢ c2 ∼ c3 ->
    policy2 ∘ policy1 ⊢ c1 ∼ c3.
Proof.
  cbv [simulates].
  intros ?? [R [S Sr]] [R' [S' Sr']].
  exists (fun s1 s3 => exists s2, R s1 s2 /\ R' s2 s3).
  propositional; [ | eapply refines_trans ] ; eauto.
Qed.
