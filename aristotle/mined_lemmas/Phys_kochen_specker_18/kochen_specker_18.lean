/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

/-! ### The 18 vectors

We use the Cabello–Estebaranz–García-Alcaine 18-vector, 9-basis Kochen–Specker set in `ℝ⁴`.
The vectors have integer coordinates, listed here as rows. -/

/-- Integer coordinates of the 18 Kochen–Specker vectors. -/

theorem kochen_specker_18 : ¬ ∃ f : Fin 18 → Bool, IsKSColoring f := by
  rintro ⟨f, hf⟩
  have c1 := ctx_sum_eq_one hf 0 1 2 3 (by decide)
  have c2 := ctx_sum_eq_one hf 0 4 5 6 (by decide)
  have c3 := ctx_sum_eq_one hf 7 8 2 9 (by decide)
  have c4 := ctx_sum_eq_one hf 7 10 6 11 (by decide)
  have c5 := ctx_sum_eq_one hf 1 4 12 13 (by decide)
  have c6 := ctx_sum_eq_one hf 8 10 13 14 (by decide)
  have c7 := ctx_sum_eq_one hf 15 16 3 9 (by decide)
  have c8 := ctx_sum_eq_one hf 15 17 5 11 (by decide)
  have c9 := ctx_sum_eq_one hf 16 17 12 14 (by decide)
  omega

end Phys

