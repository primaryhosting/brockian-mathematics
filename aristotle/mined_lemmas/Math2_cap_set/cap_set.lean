/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

namespace Math2

open Finset Filter Asymptotics

/-- The number of points of `𝔽₃ⁿ`, where `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`. -/

theorem cap_set :
    (fun n : ℕ => (capSetNumber n : ℝ)) =o[atTop] fun n : ℕ => (3 : ℝ) ^ n := by
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cap_set_density ε hε
  rw [eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨A, -, hAcard, hA⟩ :=
    addRothNumber_spec (Finset.univ : Finset (Fin n → ZMod 3))
  have h := hN n hn A hA
  rw [hAcard] at h
  calc ‖(capSetNumber n : ℝ)‖ = (capSetNumber n : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ε * 3 ^ n := h
    _ = ε * ‖(3 : ℝ) ^ n‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

end Math2

