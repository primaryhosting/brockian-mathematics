/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring; the header above is
-- repeated below as the module docstring.)
import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Finset

namespace Chem

/-- The standard additive character of `ZMod 11`, `x ↦ exp (2πI x / 11)`. -/
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod 11) ℂ)

/-- The Hückel eigenvalues of the cycle `C₁₁`. -/

theorem huckel_C11_zmod (μ : ℂ) :
    (∃ v : ZMod 11 → ℂ, v ≠ 0 ∧ Adj11.mulVec v = μ • v) ↔
      ∃ k : ZMod 11, μ = 2 * Real.cos (2 * Real.pi * k.val / 11) := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    set w := Gmat.mulVec v with hw
    have hFw : Fmat.mulVec w = v := by
      rw [hw, ← Matrix.mulVec_mulVec, Fmat_mul_Gmat, Matrix.one_mulVec]
    have hwne : w ≠ 0 := by
      intro h
      apply hv
      rw [← hFw, h, Matrix.mulVec_zero]
    have hDw : (Matrix.diagonal lam).mulVec w = μ • w := by
      have hGA : Gmat * Adj11 = Matrix.diagonal lam * Gmat := by
        calc Gmat * Adj11 = Gmat * Adj11 * (Fmat * Gmat) := by rw [Fmat_mul_Gmat, mul_one]
        _ = Gmat * (Adj11 * Fmat) * Gmat := by simp [mul_assoc]
        _ = Gmat * Fmat * (Matrix.diagonal lam * Gmat) := by
              rw [Adj11_mul_Fmat]; simp [mul_assoc]
        _ = Matrix.diagonal lam * Gmat := by rw [Gmat_mul_Fmat, one_mul]
      calc (Matrix.diagonal lam).mulVec w
          = (Matrix.diagonal lam * Gmat).mulVec v := by rw [hw, Matrix.mulVec_mulVec]
        _ = (Gmat * Adj11).mulVec v := by rw [hGA]
        _ = Gmat.mulVec (Adj11.mulVec v) := by rw [Matrix.mulVec_mulVec]
        _ = Gmat.mulVec (μ • v) := by rw [hAv]
        _ = μ • w := by rw [hw, Matrix.mulVec_smul]
    obtain ⟨k, hk⟩ : ∃ k : ZMod 11, w k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hwne (funext h)
    refine ⟨k, ?_⟩
    have := congrFun hDw k
    rw [Matrix.mulVec_diagonal] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have := mul_right_cancel₀ hk this
    rw [← this, lam]
  · rintro ⟨k, rfl⟩
    refine ⟨fun j => Fmat j k, ?_, ?_⟩
    · intro h
      have h0 : Fmat 0 k = 0 := congrFun h 0
      simp [Fmat] at h0
    · funext i
      have := congrFun (congrFun Adj11_mul_Fmat i) k
      rw [Matrix.mul_apply, Matrix.mul_apply] at this
      have hd : ∑ j : ZMod 11, Fmat i j * Matrix.diagonal lam j k = Fmat i k * lam k := by
        rw [Finset.sum_eq_single k]
        · simp [Matrix.diagonal]
        · intro b _ hb; simp [Matrix.diagonal, hb]
        · intro h; exact absurd (Finset.mem_univ k) h
      rw [hd] at this
      simpa [Matrix.mulVec, Matrix.dotProduct, lam, mul_comm] using this

/-- **Hückel theory for the cycle `C₁₁`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₁` (i.e. there is a nonzero vector `v` with `A v = μ v`)
if and only if `μ = 2 cos (2πk/11)` for some `k ∈ {0, 1, …, 10}`. -/
