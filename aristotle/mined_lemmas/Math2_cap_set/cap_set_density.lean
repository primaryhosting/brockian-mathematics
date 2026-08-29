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

theorem cap_set_density (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (#A : ℝ) ≤ ε * 3 ^ n := by
  obtain ⟨N, hN⟩ := exists_bound_le_pow ε
  refine ⟨N, fun n hn A hA => ?_⟩
  by_contra hlt
  push_neg at hlt
  refine roth_3ap_theorem ε hε ?_ A ?_ hA
  · rw [card_F3pow]; exact hN n hn
  · rw [card_F3pow]; push_cast; exact hlt.le

/-- The size of the largest cap set (3AP-free subset) in `𝔽₃ⁿ`. -/
