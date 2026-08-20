import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, A x⟫` attached to a complex matrix `A`,
seen as an operator on `EuclideanSpace ℂ (Fin d)`. -/

lemma quadForm_add (A B : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    quadForm (A + B) x = quadForm A x + quadForm B x := by
  simp [quadForm]

/-- If all eigenvalues of a Hermitian matrix are `≤ t`, its quadratic form is bounded by
`t ‖x‖²`. -/
