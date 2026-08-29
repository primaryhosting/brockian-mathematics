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

lemma exists_joint_eigenbasis_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (hdim : Module.finrank ℂ E = Fintype.card n)
    (TA TB : E →ₗ[ℂ] E) (hTA : TA.IsSymmetric) (hTB : TB.IsSymmetric) (hcomm : Commute TA TB) :
    ∃ (b : OrthonormalBasis n ℂ E) (a c : n → ℝ),
      (∀ j, TA (b j) = (a j : ℂ) • b j) ∧ (∀ j, TB (b j) = (c j : ℂ) • b j) := by
  obtain ⟨b, hb⟩ := exists_joint_eigenvector_orthonormalBasis hdim TA TB hTA hTB hcomm
  have key : ∀ j, ∃ p : ℝ × ℝ, TA (b j) = (p.1 : ℂ) • b j ∧ TB (b j) = (p.2 : ℂ) • b j := by
    intro j
    obtain ⟨α, β, h1, h2⟩ := hb j
    have hbj : b j ≠ 0 := b.toBasis.ne_zero j
    exact ⟨(α.re, β.re), by rw [re_eigenvalue_eq hTA hbj h1]; exact h1,
      by rw [re_eigenvalue_eq hTB hbj h2]; exact h2⟩
  choose p hp₁ hp₂ using key
  exact ⟨b, fun j => (p j).1, fun j => (p j).2, hp₁, hp₂⟩

/-! ### Passing from operators to matrices -/

/-- The change-of-basis matrix from the standard basis of `EuclideanSpace ℂ n` to an
orthonormal basis `b`; its columns are the vectors `b j`. -/
