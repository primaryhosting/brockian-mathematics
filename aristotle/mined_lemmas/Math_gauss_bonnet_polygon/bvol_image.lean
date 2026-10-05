import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/

lemma bvol_image (L : E3 ≃ₗᵢ[ℝ] E3) (S : Set E3) : bvol (L '' S) = bvol S := by
  have himg : closedBall (0 : E3) 1 ∩ (L '' S) = L.symm ⁻¹' (closedBall (0 : E3) 1 ∩ S) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, mem_closedBall_zero_iff]
    constructor
    · rintro ⟨hx, y, hy, rfl⟩
      simp only [LinearIsometryEquiv.symm_apply_apply]
      exact ⟨by simpa using hx, hy⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨by simpa using hx1, L.symm x, hx2, by simp⟩
  rw [bvol, bvol, himg]
  congr 1
  exact (L.symm.measurePreserving).measure_preimage_emb
    (L.symm.toMeasurableEquiv.measurableEmbedding) _

/-- An orthonormal pair in `E3` extends to an orthonormal basis. -/
