import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem countable_fixedPoints (g : E ≃ₗᵢ[ℝ] E) (hg : g * g ≠ 1) :
    {x : E | x ∈ Metric.sphere (0 : E) 1 ∧ g x = x}.Countable := by
  classical
  set V : Submodule ℝ E := LinearMap.ker (g.toLinearEquiv.toLinearMap - LinearMap.id) with hV
  have hmemV : ∀ x : E, x ∈ V ↔ g x = x := by
    intro x
    simp [hV, LinearMap.mem_ker, sub_eq_zero]
  -- the fixed subspace has dimension at most one
  have hrank : finrank ℝ V ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h2 : 2 ≤ finrank ℝ V := hcon
    have hsum : finrank ℝ V + finrank ℝ (Vᗮ : Submodule ℝ E) = 3 := by
      rw [Submodule.finrank_add_finrank_orthogonal V, finrank_euclideanSpace_fin]
    have hperp : finrank ℝ (Vᗮ : Submodule ℝ E) ≤ 1 := by omega
    have hinv : ∀ w ∈ Vᗮ, g w ∈ Vᗮ := by
      intro w hw
      rw [Submodule.mem_orthogonal]
      intro u hu
      have hgu : g u = u := (hmemV u).1 hu
      have : inner ℝ (g u) (g w) = inner ℝ u w := g.inner_map_map u w
      rw [hgu] at this
      rw [this]
      exact (Submodule.mem_orthogonal V w).1 hw u hu
    have hsq : ∀ w ∈ Vᗮ, g (g w) = w := by
      intro w hw
      rcases eq_or_ne w 0 with rfl | hw0
      · simp
      · have hle : (ℝ ∙ w) ≤ Vᗮ := by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact hw
        have hspan : (ℝ ∙ w) = Vᗮ := by
          refine Submodule.eq_of_le_of_finrank_le hle ?_
          rw [finrank_span_singleton hw0]
          exact hperp
        have hgw : g w ∈ (ℝ ∙ w) := by
          rw [hspan]
          exact hinv w hw
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hgw
        have hnorm : ‖w‖ = |c| * ‖w‖ := by
          have : ‖g w‖ = ‖w‖ := g.norm_map w
          rw [← hc, norm_smul, Real.norm_eq_abs] at this
          exact this.symm
        have habs : |c| = 1 := by
          have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
          have h1 : |c| * ‖w‖ = 1 * ‖w‖ := by rw [one_mul]; exact hnorm.symm
          exact mul_right_cancel₀ (ne_of_gt hwpos) h1
        have hcc : c * c = 1 := by
          rw [← abs_mul_abs_self, habs]; norm_num
        rw [← hc]
        show g (c • w) = w
        rw [map_smul, ← hc, smul_smul, hcc, one_smul]
    have : g * g = 1 := by
      apply LinearIsometryEquiv.ext
      intro x
      have hcompl : IsCompl V (Vᗮ : Submodule ℝ E) :=
        Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
      have hx : x ∈ V ⊔ Vᗮ := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      show g (g (v + w)) = v + w
      rw [map_add, map_add, (hmemV v).1 hv, (hmemV v).1 hv, hsq w hw]
    exact hg this
  -- hence at most two unit vectors are fixed
  rcases Set.eq_empty_or_nonempty {x : E | x ∈ Metric.sphere (0 : E) 1 ∧ g x = x} with h | ⟨x₀, hx₀⟩
  · rw [h]; exact Set.countable_empty
  · have hx₀norm : ‖x₀‖ = 1 := by
      have := hx₀.1
      rwa [mem_sphere_iff_norm, sub_zero] at this
    have hx₀0 : x₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx₀norm
      norm_num at hx₀norm
    have hx₀V : x₀ ∈ V := (hmemV x₀).2 hx₀.2
    have hspan : (ℝ ∙ x₀) = V := by
      refine Submodule.eq_of_le_of_finrank_le ?_ ?_
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hx₀V
      · rw [finrank_span_singleton hx₀0]
        exact hrank
    refine Set.Countable.mono ?_ ((Set.countable_singleton (-x₀)).insert x₀)
    rintro y ⟨hy1, hy2⟩
    have hynorm : ‖y‖ = 1 := by rwa [mem_sphere_iff_norm, sub_zero] at hy1
    have hyV : y ∈ V := (hmemV y).2 hy2
    rw [← hspan] at hyV
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hyV
    have habs : |c| = 1 := by
      have : ‖y‖ = |c| * ‖x₀‖ := by rw [← hc, norm_smul, Real.norm_eq_abs]
      rw [hynorm, hx₀norm, mul_one] at this
      exact this.symm
    have hcases : c = 1 ∨ c = -1 := by
      have hcc : c * c = 1 := by rw [← abs_mul_abs_self, habs]; norm_num
      have h1 : (c - 1) * (c + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h1 with h | h
      · left; linarith
      · right; linarith
    rcases hcases with h | h
    · left; rw [← hc, h, one_smul]
    · right; rw [Set.mem_singleton_iff, ← hc, h]; module

end BT

