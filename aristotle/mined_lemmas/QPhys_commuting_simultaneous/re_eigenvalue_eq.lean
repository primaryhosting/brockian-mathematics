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

lemma re_eigenvalue_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {x : E} (hx : x ≠ 0) {c : ℂ} (h : T x = c • x) :
    (c.re : ℂ) = c :=
  Complex.conj_eq_iff_re.1 (hT.conj_eigenvalue_eq_self
    (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 h, hx⟩))

omit [DecidableEq n] in
/-- Two commuting symmetric operators on a finite-dimensional complex inner product space have
a common orthonormal eigenbasis, with real eigenvalues. -/
