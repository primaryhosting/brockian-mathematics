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

lemma mulVec_of_toEuclideanLin_eq (A : Matrix n n ℂ) {x : EuclideanSpace ℂ n} {c : ℂ}
    (h : Matrix.toEuclideanLin A x = c • x) : A *ᵥ ⇑x = c • ⇑x := by
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using congrArg WithLp.ofLp h

/-- Two commuting Hermitian matrices have a common orthonormal eigenbasis, with real
eigenvalues. -/
