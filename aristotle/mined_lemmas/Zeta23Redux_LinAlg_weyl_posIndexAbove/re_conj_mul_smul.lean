/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real quadratic form `x ↦ ⟪x, M x⟫` attached to a matrix `M`. -/

lemma re_conj_mul_smul (mu : ℝ) (z : ℂ) :
    RCLike.re ((starRingEnd ℂ) z * ((mu : ℂ) * z)) = mu * ‖z‖ ^ 2 := by
  rw [show (starRingEnd ℂ) z * ((mu : ℂ) * z) = (mu : ℂ) * (z * (starRingEnd ℂ) z) by ring,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
  exact Complex.ofReal_re _

/-- The eigenvector basis diagonalizes the associated linear map. -/
