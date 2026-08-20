import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma det_id_add_smul_pos (A : E →L[ℝ] E) {t : ℝ} (ht : 0 ≤ t) (h : t * ‖A‖ < 1) :
    0 < (ContinuousLinearMap.id ℝ E + t • A).det := by
  by_contra hle
  push_neg at hle
  have hF0 : (ContinuousLinearMap.id ℝ E + (0 : ℝ) • A).det = 1 := by
    simp [ContinuousLinearMap.det]
  have hmem : (0 : ℝ) ∈ (fun s : ℝ => (ContinuousLinearMap.id ℝ E + s • A).det) '' (Icc 0 t) := by
    refine intermediate_value_Icc' ht (continuous_det_id_add_smul A).continuousOn ?_
    rw [mem_Icc]
    exact ⟨hle, by rw [hF0]; norm_num⟩
  obtain ⟨s, hs, hFs⟩ := hmem
  refine det_id_add_smul_ne_zero A ?_ hFs
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  have hs0 : 0 ≤ s := hs.1
  have : ‖s • A‖ = s * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  rw [this]
  nlinarith [hs.2]

/-- If `‖t • A‖ < 1` then `id + t • A` is a linear homeomorphism. -/
