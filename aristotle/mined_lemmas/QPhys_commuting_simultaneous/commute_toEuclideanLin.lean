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

lemma commute_toEuclideanLin {A B : Matrix n n ℂ} (hAB : A * B = B * A) :
    Commute (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) := by
  unfold Commute SemiconjBy
  ext x i
  simp only [Module.End.mul_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAB]

