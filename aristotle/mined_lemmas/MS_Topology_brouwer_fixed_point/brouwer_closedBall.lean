import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

theorem brouwer_closedBall (f : closedBall (0 : E) 1 → closedBall (0 : E) 1)
    (hf : Continuous f) : ∃ x, f x = x := by
  classical
  by_contra hcon
  push_neg at hcon
  have hKc : IsCompact (closedBall (0 : E) 1) := isCompact_closedBall _ _
  set φ : E → E := fun x => if hx : x ∈ closedBall (0 : E) 1 then (f ⟨x, hx⟩ : E) else 0 with hφdef
  have hφval : ∀ (x : E) (hx : x ∈ closedBall (0 : E) 1), φ x = (f ⟨x, hx⟩ : E) := by
    intro x hx; rw [hφdef]; simp only [dif_pos hx]
  have hres : (closedBall (0 : E) 1).restrict φ = fun x : closedBall (0 : E) 1 => (f x : E) := by
    funext x
    simp only [Set.restrict_apply, hφval x x.2, Subtype.coe_eta]
  have hφc : ContinuousOn φ (closedBall (0 : E) 1) := by
    rw [continuousOn_iff_continuous_restrict, hres]
    exact continuous_subtype_val.comp hf
  have hφmem : ∀ x ∈ closedBall (0 : E) 1, ‖φ x‖ ≤ 1 := by
    intro x hx
    rw [hφval x hx]
    exact mem_closedBall_zero_iff.mp (f ⟨x, hx⟩).2
  have hne : ∀ x ∈ closedBall (0 : E) 1, φ x ≠ x := by
    intro x hx h
    exact hcon ⟨x, hx⟩ (Subtype.ext ((hφval x hx).symm.trans h))
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hKc.exists_isMinOn ⟨0, by simp⟩ ((hφc.sub continuousOn_id).norm)
  set ε : ℝ := ‖φ x₀ - x₀‖ with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef, norm_pos_iff, sub_ne_zero]
    exact hne x₀ hx₀K
  have hlow : ∀ x ∈ closedBall (0 : E) 1, ε ≤ ‖φ x - x‖ := fun x hx => hx₀min hx
  set δ : ℝ := ε / 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨G, hG, hGapp⟩ := exists_contDiff_approx hKc φ hφc hδpos
  set c : ℝ := (1 + δ)⁻¹ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  set g : E → E := fun x => c • G x with hgdef
  have hgcd : ContDiff ℝ 1 g := contDiff_const.smul hG
  have hGb : ∀ x ∈ closedBall (0 : E) 1, ‖G x‖ ≤ 1 + δ := by
    intro x hx
    have hsplit : G x = φ x + (G x - φ x) := by abel
    calc ‖G x‖ = ‖φ x + (G x - φ x)‖ := by rw [← hsplit]
      _ ≤ ‖φ x‖ + ‖G x - φ x‖ := norm_add_le _ _
      _ ≤ 1 + δ := by linarith [hφmem x hx, hGapp x hx]
  have hgmaps : ∀ x ∈ closedBall (0 : E) 1, ‖g x‖ ≤ 1 := by
    intro x hx
    have h1 : ‖g x‖ = c * ‖G x‖ := by
      rw [hgdef]; simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [h1, hcdef, inv_mul_eq_div, div_le_one (by linarith)]
    exact hGb x hx
  have hgapp : ∀ x ∈ closedBall (0 : E) 1, ‖g x - φ x‖ < 2 * δ := by
    intro x hx
    have h1 : ‖g x - G x‖ ≤ δ := by
      have hgG : g x - G x = (c - 1) • G x := by rw [hgdef]; module
      have hcle : c - 1 ≤ 0 := by
        rw [hcdef, sub_nonpos]; exact inv_le_one_of_one_le₀ (by linarith)
      have hc1 : |c - 1| = δ / (1 + δ) := by
        rw [abs_of_nonpos hcle, hcdef]; field_simp; ring
      rw [hgG, norm_smul, Real.norm_eq_abs, hc1, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [hGb x hx, hδpos]
    calc ‖g x - φ x‖ ≤ ‖g x - G x‖ + ‖G x - φ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 2 * δ := by linarith [hGapp x hx]
  obtain ⟨z, hzK, hz⟩ := exists_fixedPoint_of_contDiff hgcd hgmaps
  have h1 : ε ≤ ‖φ z - z‖ := hlow z hzK
  have h2 : ‖g z - φ z‖ < 2 * δ := hgapp z hzK
  rw [hz, norm_sub_rev, hδdef] at h2
  linarith

end Main

end Brouwer

