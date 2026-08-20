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

lemma toEuclideanLin_eigenvectorBasis {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (j : Fin d) :
    (Matrix.toEuclideanLin A) (hA.eigenvectorBasis j)
      = (hA.eigenvalues j : ℂ) • hA.eigenvectorBasis j := by
  have h := hA.mulVec_eigenvectorBasis j
  apply WithLp.ofLp_injective (p := 2)
  simp [Matrix.toEuclideanLin, h]

/-- Diagonalization of the quadratic form in the eigenbasis. -/
