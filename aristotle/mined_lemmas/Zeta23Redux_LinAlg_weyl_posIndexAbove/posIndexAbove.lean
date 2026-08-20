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

noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (theta : ℝ) : ℕ :=
  (Finset.univ.filter fun i => theta < hA.eigenvalues i).card

/-- **Weyl monotonicity of the positive index**: if `A` and `E` are Hermitian and every
eigenvalue of `E` has absolute value at most `theta`, then the number of eigenvalues of
`A + E` strictly above `theta` is at most the number of strictly positive eigenvalues
of `A`. -/
