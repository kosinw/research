(****************************************************************************)
(*  ToyMultiplier.v                                                         *)
(*                                                                          *)
(*  A small, bit-serial (shift-and-add) multiplier written over a simple    *)
(*  bitvector library (`Zmod`).                                             *)
(*                                                                          *)
(*  High-level algorithm (classic shift-and-add):                           *)
(*  - The 2W-bit register `P` holds both the partial sum (upper W+1 bits)   *)
(*    and the shifting multiplier (lower W-1 bits).                         *)
(*  - Each cycle, if the current least-significant bit of `P` is 1, we add  *)
(*    the multiplicand `B` into the upper part of `P`.                      *)
(*  - Then we effectively shift `P` right by one bit by re-assembling the   *)
(*    upper (W+1)-bit segment with the (W-1)-bit tail of the lower segment. *)
(*  - After W cycles, the full product is available in `P`.                 *)
(*                                                                          *)
(*  The state machine exposes a very small handshake-like interface via     *)
(*  `IOEvent` and a simple leak model via `LeakageEvent`.                   *)
(****************************************************************************)

From Stdlib Require Import Zmod.
From Stdlib Require Import List. Import ListNotations.

(*
  Bit-level notations, all living in scope `bits_scope`.
  - `x # n` constructs an n-bit value from integer x (mod 2^n).
  - `a =? b` is bitvector equality.
  - `x #[ i ]` is the single-bit slice at index i.
  - `x .[ hi , lo ]` is the inclusive slice from lo to hi.
  - `a ++ b` concatenates `a` above `b` (note the argument order of `Zmod.app`).
  - `+`, `-`, `*` are bitvector arithmetic modulo the bitwidth.
*)
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

Section WithWidth.
  Context {W : Z}.
  Local Open Scope bits_scope.

  #[warnings="-notation-for-abbreviation"]
    Local Notation WP := (Z.mul 2 W) (only parsing).

  #[warnings="-notation-for-abbreviation"]
    Local Notation WC := (Z.log2_up W) (only parsing).

  (*
    Architectural state of the multiplier:
    - `B`   : multiplicand (W bits), latched at start, constant during run
    - `A`   : partial product and shifting multiplier (2W bits)
    - `Cnt` : countdown cycles remaining (enough bits to count up to W)
    - `Busy`: 1 when an operation is in progress, 0 when idle
  *)
  Record Registers : Set :=
    mkRegisters
    { B : bits W
    ; A : bits WP
    ; Cnt : bits WC
    ; Busy : bits 1
    }.

  (* Architectural reset state *)
  Definition R0 : Registers := mkRegisters 0#W 0#WP 0#WC 0#1.

  (* Simple leakage model. Currently only `LeakValid` is used to model a
     leak on valid/ready-like events. Included as options in a trace. *)
  Inductive LeakageEvent : Set :=
  | LeakValid
  | LeakReady
  | LeakNone.

  Definition LeakageTrace := list LeakageEvent.

  (* External IO events: input of two W-bit operands, and output of a 2W-bit product. *)
  Inductive IOEvent : Set :=
  | IOIn (a b : bits W)
  | IOOut (p : bits WP)
  | IONone.

  Definition IOTrace := list IOEvent.

  (* Tiny command DSL to script example scenarios. *)
  Inductive Cmd : Set :=
  | CmdValid (a b : bits W)
  | CmdSkip
  | CmdSeq (c1 c2 : Cmd).

  Declare Scope cmd_scope.
  Delimit Scope cmd_scope with cmd.

  Notation "'skip'" := CmdSkip : cmd_scope.

  Notation "'valid' a b" := (CmdValid a b)
                              (at level 10, a at level 9, b at level 9) : cmd_scope.

  Notation "c1 ';' c2" := (CmdSeq c1 c2)
                            (at level 51, right associativity) : cmd_scope.

  Bind Scope cmd_scope with Cmd.

  Local Open Scope cmd_scope.

  (* Zero-extension helper: turn a bitvector `b` into a larger bitvector of
     width `z` by reinterpreting its unsigned value. *)
  Definition zext {n} (z : Z) (b : bits n) := (Zmod.unsigned b)#z.

  (* Represents a postcondition in the omnisemantics sense. Since we only really
     care about calculating the leakage trace as some function of the IOTrace and
     values of initial state (which will usually appear in a quantifier). *)
  Definition Post := Registers -> IOTrace -> LeakageTrace -> Prop.

  Declare Scope post_scope.
  Delimit Scope post_scope with post.

  Definition Post_implies (P Q : Post) : Prop :=
    forall r t k, P r t k -> Q r t k.

  Notation "P ->> Q" := (Post_implies P Q)
                          (at level 80) : post_scope.

  Bind Scope post_scope with Post.

  Local Open Scope post_scope.

  (* TODO kosinw: This definition relies heavily on dependent types; however,
     since I cannot get it to run quickly I'm disable it for now. *)

  (**********************************************************************)
  (* Definition cast_bits {n m : Z} (pf : n = m) (x : bits n) : bits m. *)
  (* Proof.                                                             *)
  (*   rewrite <- pf.                                                   *)
  (*   exact x.                                                         *)
  (* Defined.                                                           *)
  (*                                                                    *)
  (* Definition wid_t0 : (WP - 1 + 1 - W + 1 = W + 1)%Z.                *)
  (* Proof using W.                                                     *)
  (*   rewrite Z.sub_add.                                               *)
  (*   rewrite <- Z.mul_pred_l.                                         *)
  (*   replace (Z.pred 2%Z) with 1%Z by exact eq_refl.                  *)
  (*   rewrite Z.mul_1_l.                                               *)
  (*   exact eq_refl.                                                   *)
  (* Defined.                                                           *)
  (*                                                                    *)
  (* Definition wid_p' : (W - 1 + 1 - 1 + (W + 1) = WP)%Z.              *)
  (* Proof using W.                                                     *)
  (*   rewrite Z.sub_add.                                               *)
  (*   replace (W + 1)%Z with (1 + W)%Z by apply Z.add_comm.            *)
  (*   rewrite Z.add_assoc.                                             *)
  (*   rewrite Z.sub_add.                                               *)
  (*   rewrite Z.add_diag.                                              *)
  (*   exact eq_refl.                                                   *)
  (* Defined.                                                           *)
  (*                                                                    *)
  (* Definition compute_p' (b : bits W) (p : bits WP) : bits WP.        *)
  (* Proof using W.                                                     *)
  (*   refine (                                                         *)
  (*       let t0 := cast_bits wid_t0 (0#1 ++ p.[WP-1,W]) in            *)
  (*       let t1 := if p#[0] =? 1#1 then 0#1 ++ b else 0#(W+1) in      *)
  (*       cast_bits wid_p' ((t0 + t1) ++ p.[W-1,1])                    *)
  (*     ).                                                             *)
  (* Defined.                                                           *)
  (**********************************************************************)

  (*
    Core datapath step for the bit-serial multiplier.
    Given multiplicand `b` and current `p`:
    - `t0` is the upper half of `p` (bits [WP-1:W]) zero-extended to W+1 bits;
      this provides space for the carry of the addition.
    - `t1` is either `b` (zero-extended to W+1) when the lsb `p#[0]` is 1,
      or zero otherwise. This encodes the conditional add.
    - We add `t0` and `t1` (W+1 bits), then append the lower half of `p`
      shifted right by one (`p.[W-1,1]`), reconstructing a new 2W-bit `p`.
  *)
  Definition compute_a' (b : bits W) (p : bits WP) : bits WP :=
    let t0 := zext (W+1) p.[WP-1,W] in
    let t1 := if p#[0] =? 1#1 then zext (W+1) b else 0#(W+1) in
    zext WP ((t0 + t1) ++ p.[W-1,1]).

  (*
    One machine cycle.
    - When idle (`Busy = 0`):
        * If input `(a,b)` is present, load `P <- a`, `B <- b`,
          set `Cnt <- W-1`, and go busy. Emit IO and leak events.
        * Else remain idle.
    - When busy:
        * Update `P <- compute_p' B P`.
        * Decrement `Cnt`; when it reaches 0, finish the operation,
          drive `IOOut P` and deassert `Busy`.
  *)
  Definition cycle (r : Registers) (i : option (bits W * bits W))
    : Registers * IOEvent * LeakageEvent :=
    if r.(Busy) =? 0#1
    then (
        match i with
        | Some (a, b) =>
            let p' := zext WP a in
            let b' := b in
            let cnt' := (W-1)#WC in
            let busy' := 1#1 in
            (mkRegisters b' p' cnt' busy', IOIn a b, LeakValid)
        | None => (r, IONone, LeakNone)
        end
      )
    else (
        let p' := compute_a' r.(B) r.(A) in
        let cnt' := if (r.(Cnt) =? 0#WC) then 0#WC else r.(Cnt) - 1#WC in
        let busy' := if (r.(Cnt) =? 0#WC) then 0#1 else 1#1 in
        let out' := if (r.(Cnt) =? 0#WC) then IOOut p' else IONone in
        let leak' := if (r.(Cnt) =? 0#WC) then LeakReady else LeakNone in
        (mkRegisters r.(B) p' cnt' busy', out', leak')
      ).

  Reserved Notation "s ⇓ Q" (at level 71, left associativity).

  Local Open Scope list_scope.

  Inductive eval : Cmd -> Registers -> IOTrace -> LeakageTrace -> Post -> Prop :=
  | EvalSeq : forall c1 c2 r t k Q1 Q,
      (c1, r, t, k) ⇓ Q1 ->
      (forall r' t' k', Q1 r' t' k' -> eval c2 r' t' k' Q) ->
      (c1 ; c2, r, t, k) ⇓ Q

  | EvalValid : forall a b r t k Q r' io leak,
      cycle r (Some (a, b)) = (r', io, leak) ->
      Q r' (t ++ [io]) (k ++ [leak]) ->
      (CmdValid a b, r, t, k) ⇓ Q

  | EvalSkip : forall r t k Q r' io leak,
      cycle r None = (r', io, leak) ->
      Q r' (t ++ [io]) (k ++ [leak]) ->
      (CmdSkip, r, t, k) ⇓ Q

  where "s ⇓ Q" := (let '(c, r, t, k) := s in eval c r t k Q).

  Lemma weaken_post : forall s P Q,
      P ->> Q -> s ⇓ Q -> s ⇓ P.
  Proof.
    intros; simpl.
    destruct s as [[[c r] t] k]; subst.
    inversion H0; subst.
    - admit.
    - econstructor.
      eassumption.
      unfold Post_implies in H.

  Example ex_eval1 : (skip%cmd, R0, [], []) ⇓ (fun _ _ _ => True).
  Proof using W.
    econstructor.
    econstructor.
    exact I.
  Qed.
End WithWidth.
