From research Require Import base bit circuit.
From stdpp Require Import fin finite vector.

Module RegFile.
  Section WithContext.
    Context (b : N) (sz : N) {H0 : BvWf b 0} {H1 : BvWf sz 0}.

    Record t := { contents : Vector (Bit b) (card (Bit sz)) }.

    Definition mk := {| contents := mkVector 0%bv (card (Bit sz)) |}.

    Definition sub (addr : Bit sz) (t : t) :=
      if decide (addr = 0)%bv then
        0%bv
      else
        t.(contents) !!! encode_fin addr.

    Definition upd (addr : Bit sz) (data : Bit b) :=
      {{ let%modify contents := vinsert (encode_fin addr) data in
         pass
      }}.
  End WithContext.

  Arguments mk {_ _ _}.
  Arguments sub {_ _ _ _}.
  Arguments upd {_ _}.
End RegFile.
