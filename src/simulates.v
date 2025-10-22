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

Definition simulates `(c1 : Circuit t1 m1) `(c2 : Circuit t2 m2) (policy : m1 -> m2) :=
  exists R, R c1.(init) c2.(init) /\ refines c1 c2 policy R.

Notation "P ⊢ c1 ⊑ c2" := (simulates c1 c2 P) (at level 60, c1 at next level).
