import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

lemma exists_eigenvector_iff_det_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {K : Type*}
    [Field K] (M : Matrix n n K) (μ : K) :
    (∃ v : n → K, v ≠ 0 ∧ M *ᵥ v = μ • v) ↔ (M - μ • 1).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h

/-- If `v` is an eigenvector of `M` with eigenvalue `c`, it is an eigenvector of `M ^ d`. -/
