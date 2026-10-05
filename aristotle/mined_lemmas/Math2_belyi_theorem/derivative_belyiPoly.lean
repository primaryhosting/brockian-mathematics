import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/

lemma derivative_belyiPoly (a b : ℕ) :
    derivative (belyiPoly a b) =
      C (belyiC a b) *
        (X ^ a * ((1 - X) ^ b * (C ((a : ℚ) + 1) - C ((a : ℚ) + b + 2) * X))) := by
  unfold belyiPoly
  simp only [derivative_mul, derivative_C, derivative_pow, derivative_X,
    derivative_one, zero_mul, zero_add, mul_one, zero_sub, Nat.add_sub_cancel,
    map_add, map_sub, map_natCast, C_1, map_ofNat]
  push_cast
  ring

