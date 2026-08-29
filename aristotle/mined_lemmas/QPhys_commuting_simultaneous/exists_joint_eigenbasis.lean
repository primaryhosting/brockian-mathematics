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

lemma exists_joint_eigenbasis {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A * B = B * A) :
    ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a c : n → ℝ),
      (∀ j, A *ᵥ ⇑(b j) = (a j : ℂ) • ⇑(b j)) ∧ (∀ j, B *ᵥ ⇑(b j) = (c j : ℂ) • ⇑(b j)) := by
  obtain ⟨b, a, c, ha, hc⟩ := exists_joint_eigenbasis_real
    (E := EuclideanSpace ℂ n) finrank_euclideanSpace _ _
    (Matrix.isHermitian_iff_isSymmetric.1 hA) (Matrix.isHermitian_iff_isSymmetric.1 hB)
    (commute_toEuclideanLin hAB)
  exact ⟨b, a, c, fun j => mulVec_of_toEuclideanLin_eq A (ha j),
    fun j => mulVec_of_toEuclideanLin_eq B (hc j)⟩

/-- **Commuting Hermitian operators are simultaneously diagonalizable.**
Given two commuting Hermitian matrices `A` and `B` there is a single unitary matrix `U` and
real vectors `a`, `c` such that `Uᴴ A U` and `Uᴴ B U` are the diagonal matrices with diagonals
`a` and `c`. -/
