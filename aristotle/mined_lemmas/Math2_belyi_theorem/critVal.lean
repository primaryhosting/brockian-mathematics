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

def critVal (f : ℚ[X]) : Set ℂ :=
  {v | ∃ w : ℂ, aeval w (derivative f) = 0 ∧ aeval w f = v}

/-- `f` is a *Belyi map*: a nonconstant morphism `ℙ¹ → ℙ¹`, defined over `ℚ`, whose branch
locus is contained in `{0, 1, ∞}`.  (A polynomial map is totally ramified over `∞`, so the
only remaining condition is that all finite critical values lie in `{0,1}`.) -/
