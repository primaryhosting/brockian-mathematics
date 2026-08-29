import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Matrix Module.End

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### A common orthonormal eigenbasis for two commuting symmetric operators -/

omit [DecidableEq n] in
/-- Two commuting symmetric operators on a finite-dimensional complex inner product space
have a common orthonormal eigenbasis. -/

lemma conjTranspose_obMatrix_mulVec (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (j : n) :
    (obMatrix b)ᴴ *ᵥ ⇑(b j) = Pi.single j 1 := by
  have h1 : (obMatrix b)ᴴ * obMatrix b = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := obMatrix b)).1 (obMatrix_mem_unitaryGroup b)
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [← obMatrix_mulVec_single b j, mulVec_mulVec, h1, one_mulVec]

/-- If every vector of an orthonormal basis `b` is an eigenvector of `M`, then conjugating `M`
by the unitary matrix `obMatrix b` diagonalizes `M`. -/
