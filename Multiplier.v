Set Implicit Arguments.

Require Import Frap.
From Stdlib Require Import Zmod.

Declare Scope bits_scope.
Delimit Scope bits_scope with bits.

Notation "x # n" :=
  (bits.of_Z n x)
    (at level 0, format "x # n") : bits_scope.
Notation "a =? b" :=
  (@Zmod.eqb _ a b) (at level 70) : bits_scope.
Notation "x #[ i ]" :=
  (Zmod.slice i (i+1) x)
    (at level 2, right associativity, format "x #[ i ]") : bits_scope.
Notation "x .[ hi , lo ]" :=
  (Zmod.slice lo (hi+1) x)
    (format "x .[ hi , lo ]") : bits_scope.
Notation "a ++ b" := (Zmod.app b a) (format "a ++ b") : bits_scope.
Notation "a + b" := (Zmod.add a b) (format "a + b") : bits_scope.
Notation "a - b" := (Zmod.sub a b) (format "a - b") : bits_scope.
Notation "a * b" := (Zmod.mul a b) (format "a * b") : bits_scope.

Definition cast_bits {n m : Z} (pf : n = m) (x : bits n) : bits m.
Proof.
  rewrite <- pf.
  exact x.
Defined.

Module Simple. Section WithWidth.
  Context {W : Z}.
  Local Open Scope bits_scope.

  #[warnings="-notation-for-abbreviation"]
  Local Notation WP := (2*W)%Z (only parsing).

  #[warnings="-notation-for-abbreviation"]
  Local Notation WC := (Z.log2_up W) (only parsing).

  Record R : Set :=
    mk_R
      { r_b    : bits W
      ; r_p    : bits WP
      ; r_cnt	 : bits WC
      ; r_busy : bits 1;
      }.

  Definition R0 : R := mk_R 0 0 0 0.

  Definition zext {n} (z : Z) (b : bits n) : bits z :=
    bits.of_Z z (Zmod.to_Z b).

  Definition start (a : bits W) (b : bits W) : R :=
    mk_R a (zext WP b) (W-1)#WC 1#1.

  (* TODO kosinw: This definition relies heavily on dependent types; however,
     since I cannot get it to run quickly I'm disable it for now. *)

  (*****************************************************************)
  (* Definition wid_t0 : (WP - 1 + 1 - W + 1 = W + 1)%Z.           *)
  (* Proof using W.                                                *)
  (*   rewrite Z.sub_add.                                          *)
  (*   rewrite <- Z.mul_pred_l.                                    *)
  (*   replace (Z.pred 2%Z) with 1%Z by exact eq_refl.             *)
  (*   rewrite Z.mul_1_l.                                          *)
  (*   exact eq_refl.                                              *)
  (* Defined.                                                      *)
  (*                                                               *)
  (* Definition wid_p' : (W - 1 + 1 - 1 + (W + 1) = WP)%Z.         *)
  (* Proof using W.                                                *)
  (*   rewrite Z.sub_add.                                          *)
  (*   replace (W + 1)%Z with (1 + W)%Z by apply Z.add_comm.       *)
  (*   rewrite Z.add_assoc.                                        *)
  (*   rewrite Z.sub_add.                                          *)
  (*   rewrite Z.add_diag.                                         *)
  (*   exact eq_refl.                                              *)
  (* Defined.                                                      *)
  (*                                                               *)
  (* Definition compute_p' (b : bits W) (p : bits WP) : bits WP.   *)
  (* Proof using W.                                                *)
  (*   refine (                                                    *)
  (*       let t0 := cast_bits wid_t0 (0#1 ++ p.[WP-1,W]) in       *)
  (*       let t1 := if p#[0] =? 1#1 then 0#1 ++ b else 0#(W+1) in *)
  (*       cast_bits wid_p' ((t0 + t1) ++ p.[W-1,1])               *)
  (*     ).                                                        *)
  (* Defined.                                                      *)
  (*****************************************************************)

  Definition compute_p' (b : bits W) (p : bits WP) : bits WP :=
    let t0 := zext (W+1) (0#1 ++ p.[WP-1,W]) in
    let t1 := if p#[0] =? 1#1 then 0#1 ++ b else 0#(W+1) in
    zext WP ((t0 + t1) ++ p.[W-1,1]).

  Definition cycle (r : R) : R :=
    if r_busy r =? 0#1
    then r
    else (
        let b := r_b r in
        let p := r_p r in
        let cnt := r_cnt r in
        let busy := r_busy r in
        let p' := compute_p' b p in
        let cnt' := if (cnt =? 0#WC) then 0#WC else cnt - 1#WC in
        let busy' := if (cnt =? 0#WC) then 0#1 else 1#1 in
        mk_R b p' cnt' busy').

  Fixpoint cycles (n : nat) : R -> R :=
    match n with
    | O => id
    | S n => fun r => cycle (cycles n r)
    end.

  Definition Input : Set := bits W * bits W.

  Definition Output : Set := bits WP.

  Inductive LeakageEvent : Set :=
  | LLeak.

  Definition L : Set := list LeakageEvent.

  Inductive IOEvent : Set :=
  | IInput (input : Input)
  | IOutput (output : Output).

  Definition I : Set := list IOEvent.

  Inductive Command : Set :=
  | CValid (input : Input)
  | CInvalid.

  Definition C : Set := list Command.

  Definition Assertion : Type := R -> I -> L -> Prop.

  Definition State : Set := C * R * I * L.

  Definition busy (r : R) : Prop :=  r_busy r = 1%Zmod.

  Inductive Eval : State -> Assertion -> Prop :=
    | EvalSeq : forall ch ct r is ls P Q,
        Eval ([ch], r, is, ls) Q ->
        (forall r' is' ls', Q r' is' ls' -> Eval (ct, r', is', ls') P) ->
        Eval (ch :: ct, r, is, ls) P
    | EvalValid1 : forall a b r is ls P,
        ~ busy r ->
        Eval ([], start a b, IInput (a, b) :: is, ls) P ->
        Eval ([CValid (a, b)], r, is, ls) P
    | EvalValid2 : forall a b r is ls P,
        busy r ->
        Eval ([], r, is, ls) P ->
        Eval ([CValid (a, b)], r, is, ls) P
    | EvalInvalid : forall r is ls P,
        Eval ([], r, is, ls) P ->
        Eval ([CInvalid], r, is, ls) P
    | EvalCycle : forall r is ls P Q,
        busy r ->
        Eval ([], cycle r, is, ls) Q ->
        (forall r' is' ls', Q r' is' ls' -> Eval ([], r', is', ls') P) ->
        Eval ([], r, is, ls) P.

End WithWidth. End Simple.

Section Simple32.
  Local Open Scope bits_scope.

  Let s := Simple.start 5#8 6#8.

  Eval compute in s.
  Eval compute in Simple.cycles 32 s.
End Simple32.
