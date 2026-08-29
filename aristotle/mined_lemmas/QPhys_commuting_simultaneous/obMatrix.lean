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

noncomputable def obMatrix (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) : Matrix n n ℂ :=
  (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b.toBasis

