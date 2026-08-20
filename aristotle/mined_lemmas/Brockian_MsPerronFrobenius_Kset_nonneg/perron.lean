import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

theorem perron (n : ℕ) (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (hpos : ∀ i j, 0 < M i j) :
    ∃ (l : ℝ) (v : Fin n → ℝ), 0 < l ∧ (∀ i, 0 < v i) ∧ M.mulVec v = l • v := by
  obtain ⟨δ, B, hδ, hδn, hB, hnorm⟩ := exists_delta hn hpos
  -- the uniform probability vector belongs to `Kset n δ`
  have hunif : (fun _ : Fin n => (n : ℝ)⁻¹) ∈ Kset n δ := by
    refine ⟨fun i => hδn, ?_⟩
    simp [Finset.card_univ]
    field_simp
  have hCne : (Cset M δ).Nonempty :=
    ⟨(0, fun _ => (n : ℝ)⁻¹), le_refl 0, hunif, by
      intro i
      have := mulVec_pos hpos (fun i => Kset_nonneg hδ.le hunif i) (Kset_ne_zero hunif) i
      simpa using this.le⟩
  have hCcomp : IsCompact (Cset M δ) := isCompact_Cset M hδ hB
  obtain ⟨p, hpC, hpmax⟩ := hCcomp.exists_isMaxOn hCne (continuous_fst.continuousOn)
  obtain ⟨hp0, hpK, hpineq⟩ := hpC
  set r := p.1 with hrdef
  set v := p.2 with hvdef
  -- `r` is positive
  have hrpos : 0 < r := by
    obtain ⟨t, ht0, ht⟩ := exists_pos_ratio hn hpos hδ hunif
    have : t ≤ r :=
      hpmax (show ((t, fun _ : Fin n => (n : ℝ)⁻¹) : ℝ × (Fin n → ℝ)) ∈ Cset M δ from
        ⟨ht0.le, hunif, ht⟩)
    linarith
  -- `M v = r v`
  have heq : M.mulVec v = r • v := by
    by_contra hne
    obtain ⟨ε, hε, u, huK, hu⟩ := exists_improve hn hpos hδ hnorm hpK hpineq hne
    have : r + ε ≤ r := hpmax (show ((r + ε, u) : ℝ × (Fin n → ℝ)) ∈ Cset M δ from
      ⟨by linarith, huK, hu⟩)
    linarith
  exact ⟨r, v, hrpos, fun i => lt_of_lt_of_le hδ (hpK.1 i), heq⟩

end Brockian.MsPerronFrobenius

