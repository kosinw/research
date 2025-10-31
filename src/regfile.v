From research Require Import base bit circuit.
From stdpp Require Import fin finite vector.

Section WithContext.
  Context (b : N) (sz : N).

  Record RegFile := { regFileContents : Vector (Bit b) (card (Bit sz)) }.

  Definition mkRegFile := {| regFileContents := mkVector δ (card (Bit sz)) |}.

  Definition regFileSub (addr : Bit sz) (t : RegFile) :=
    if decide (addr = δ)%bv then δ else t.(regFileContents) !!! encode_fin addr.

  Definition regFileUpd (addr : Bit sz) (data : Bit b) :=
    {{ let%modify _ := vinsert (encode_fin addr) data on regFileContents in
       pass
    }}.
End WithContext.

Arguments mkRegFile {_ _}.
Arguments regFileSub {_ _}.
