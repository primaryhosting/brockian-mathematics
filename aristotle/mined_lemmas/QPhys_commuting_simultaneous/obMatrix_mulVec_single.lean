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

lemma obMatrix_mulVec_single (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (j : n) :
    obMatrix b *ᵥ Pi.single j 1 = ⇑(b j) := by
  rw [mulVec_single_one]; rfl

