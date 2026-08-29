import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
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

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The Rayleigh quadratic form of a matrix `M` at a vector `x` of Euclidean space:
`Re ⟪x, M x⟫`. -/

lemma posIndex_eq_posIndexAbove_zero {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    posIndex hA = posIndexAbove hA 0 := rfl

/-- The eigenvector basis diagonalizes the matrix, viewed as a linear map on Euclidean space. -/
