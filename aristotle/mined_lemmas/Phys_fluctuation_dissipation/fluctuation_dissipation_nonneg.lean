/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Boltzmann weight `e^{-β H(i)}` of the microstate `i`. -/

theorem fluctuation_dissipation_nonneg (β : ℝ) (hβ : 0 ≤ β) (H A : ι → ℝ) :
    0 ≤ deriv (fun l : ℝ => thermalAvg β (fun j => H j - l * A j) A) 0 := by
  rw [fluctuation_dissipation_variance]
  exact mul_nonneg hβ (sub_nonneg.mpr (sq_thermalAvg_le β H A))

end Phys

