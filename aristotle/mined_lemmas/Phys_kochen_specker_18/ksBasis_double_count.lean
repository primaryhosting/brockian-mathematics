import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Statement: An explicit 18-vector Kochen–Specker set in ℝ⁴ has no {0,1} coloring.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/

theorem ksBasis_double_count (g : Fin 18 → ℕ) :
    ∑ b : Fin 9, ∑ i : Fin 4, g (ksBasis b i) = 2 * ∑ j : Fin 18, g j := by
  simp [ksBasis, Fin.sum_univ_succ]
  ring

/-- **Kochen–Specker (18 vectors).**  There is no `{0,1}`-coloring of the 18 vectors of
`ksVec` such that in each of the 9 orthogonal bases exactly one vector is colored `1`. -/
