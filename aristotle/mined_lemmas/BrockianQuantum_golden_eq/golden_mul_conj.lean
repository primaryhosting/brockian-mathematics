import Mathlib
/-!
# Batch 12 — cyclotomic-5 and golden-ratio identities (Brockian five). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Polynomial Real

set_option autoImplicit false

/- In the Mathlib version used here, `goldConj` is called `Real.goldenConj`; the local
notation below lets the statements below be written exactly as given, while referring to
Mathlib's definition. -/
local notation "goldConj" => Real.goldenConj


theorem golden_mul_conj : goldenRatio * goldConj = -1 := Real.goldenRatio_mul_goldenConj
