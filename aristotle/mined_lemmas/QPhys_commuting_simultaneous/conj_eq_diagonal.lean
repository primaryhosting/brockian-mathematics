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

lemma conj_eq_diagonal (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (M : Matrix n n ℂ)
    (d : n → ℂ) (h : ∀ j, M *ᵥ ⇑(b j) = d j • ⇑(b j)) :
    (obMatrix b)ᴴ * M * obMatrix b = Matrix.diagonal d := by
  have hcol : ∀ j, ((obMatrix b)ᴴ * M * obMatrix b) *ᵥ Pi.single j 1 = Pi.single j (d j) := by
    intro j
    rw [← mulVec_mulVec, ← mulVec_mulVec, obMatrix_mulVec_single, h j, mulVec_smul,
      conjTranspose_obMatrix_mulVec]
    ext i
    simp [Pi.single_apply]
  ext i j
  have h1 := congrFun (hcol j) i
  rw [mulVec_single_one] at h1
  by_cases hij : i = j
  · subst hij; simpa using h1
  · rw [Matrix.diagonal_apply_ne _ hij]
    simpa [Pi.single_apply, hij] using h1

