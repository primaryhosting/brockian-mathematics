/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
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

namespace Frontier

/-! ## The tilt: inverse limit along Frobenius -/

section Tilt

variable (p : ℕ) (R : Type*) [CommRing R] [Fact p.Prime] [CharP R p]

/-- The **tilt** of a commutative ring `R` of characteristic `p`: the inverse limit
`lim_{x ↦ x^p} R`, realised as the subring of sequences `f : ℕ → R` satisfying
`f (n+1) ^ p = f n`. -/

theorem frobenius_bijective_of_perfectoid_charP (hK : IsPerfectoidField p K Γ₀) :
    Function.Bijective (frobenius K p) := by
  have hp : (p : K) = 0 := CharP.cast_eq_zero K p
  have hsurj_int : ∀ x : K, Valued.v x ≤ (1 : Γ₀) → ∃ y : K, y ^ p = x := by
    intro x hx
    obtain ⟨y, z, _, _, hyz⟩ := hK.frobenius_surjective x hx
    exact ⟨y, by have hz : x - y ^ p = 0 := by rw [hyz, hp, zero_mul]
                 linear_combination -hz⟩
  refine ⟨frobenius_inj K p, ?_⟩
  intro x
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [frobenius_def, hx0, zero_pow (Nat.Prime.pos (Fact.out (p := p.Prime))).ne']⟩
  by_cases hx : Valued.v x ≤ (1 : Γ₀)
  · obtain ⟨y, hy⟩ := hsurj_int x hx
    exact ⟨y, by simpa [frobenius_def] using hy⟩
  · push_neg at hx
    have hinv : Valued.v x⁻¹ ≤ (1 : Γ₀) := by
      rw [map_inv₀]
      exact le_of_lt (by
        rw [inv_lt_one₀ (lt_of_le_of_lt zero_le' hx)]
        exact hx)
    obtain ⟨y, hy⟩ := hsurj_int x⁻¹ hinv
    refine ⟨y⁻¹, ?_⟩
    simp only [frobenius_def, inv_pow, hy, inv_inv]

/-- Conversely, a complete perfect valued field of characteristic `p` with nontrivial,
non-discrete valuation is perfectoid.  So in equal characteristic `p`, "perfectoid" is exactly
"perfect". -/
