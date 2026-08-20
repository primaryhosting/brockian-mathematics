import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Module Submodule

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]

/-- The (real) quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`. -/

lemma posIndex_zero : posIndex (0 : Matrix m m 𝕜) = 0 := by
  have hz : ∀ i, (isHermitian_zero (n := m) (α := 𝕜)).eigenvalues i = 0 := by
    have h := (Matrix.IsHermitian.eigenvalues_eq_zero_iff
      (isHermitian_zero (n := m) (α := 𝕜))).2 rfl
    exact fun i => congrFun h i
  rw [posIndex_eq_card (isHermitian_zero (n := m) (α := 𝕜))]
  have : IsEmpty {i : m // 0 < (isHermitian_zero (n := m) (α := 𝕜)).eigenvalues i} :=
    ⟨fun i => by simpa [hz i] using i.2⟩
  simp

/-- The identity matrix is positive definite: all `card m` of its eigenvalues are positive. -/
