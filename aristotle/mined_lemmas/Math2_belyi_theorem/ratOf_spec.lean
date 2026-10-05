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

lemma ratOf_spec {z : ℂ} (h : degQ z = 1) : ((ratOf z : ℚ) : ℂ) = z := by
  have hex : ∃ q : ℚ, (q : ℂ) = z := (degQ_eq_one_iff z).mp h
  rw [ratOf, dif_pos hex]
  exact hex.choose_spec

/-- The hard direction of Belyi's theorem: a finite set of algebraic numbers admits a Belyi map
carrying it into `{0, 1}`. -/
