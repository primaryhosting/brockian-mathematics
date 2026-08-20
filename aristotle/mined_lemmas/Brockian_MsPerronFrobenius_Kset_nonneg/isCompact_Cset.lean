import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

lemma isCompact_Cset (M : Matrix (Fin n) (Fin n) ℝ) {δ B : ℝ} (hδ : 0 < δ)
    (hB : ∀ i j, M i j ≤ B) : IsCompact (Cset M δ) := by
  by_cases hB_nonneg : B ≥ 0
  · -- Case B ≥ 0: Cset M δ is a closed subset of [0, B/δ] × Kset n δ
    have hBdiv : B / δ ≥ 0 := div_nonneg hB_nonneg (le_of_lt hδ)
    -- Cset is closed
    have hclosed : IsClosed (Cset M δ) := by
      simp only [Cset]
      apply IsClosed.inter
      · exact isClosed_le continuous_const continuous_fst
      · apply IsClosed.inter
        · exact isCompact_Kset n (le_of_lt hδ) |>.isClosed.preimage continuous_snd
        · change IsClosed {p : ℝ × (Fin n → ℝ) | ∀ i, p.1 * p.2 i ≤ M.mulVec p.2 i}
          rw [show {p : ℝ × (Fin n → ℝ) | ∀ i, p.1 * p.2 i ≤ M.mulVec p.2 i} = ⋂ i, {p | p.1 * p.2 i ≤ M.mulVec p.2 i} by ext; simp]
          apply isClosed_iInter
          intro i
          have h1 : Continuous (fun p : ℝ × (Fin n → ℝ) => p.1 * p.2 i) := continuous_fst.mul ((continuous_apply i).comp continuous_snd)
          have h2 : Continuous (fun p : ℝ × (Fin n → ℝ) => M.mulVec p.2 i) := by
            simp only [Matrix.mulVec, dotProduct]
            exact continuous_finset_sum _ (fun j _ => continuous_const.mul ((continuous_apply j).comp continuous_snd))
          exact isClosed_le h1 h2
    -- Cset M δ ⊆ [0, B/δ] × Kset n δ
    have hsubset : Cset M δ ⊆ Set.Icc 0 (B / δ) ×ˢ Kset n δ := by
      intro p hp
      obtain ⟨ht, hxKset, hineq⟩ := hp
      simp only [Set.mem_prod, Set.mem_Icc]
      refine ⟨⟨ht, ?_⟩, hxKset⟩
      have hn : 0 < n := by
        by_contra hn0
        have hn0' : n = 0 := Nat.eq_zero_of_not_pos hn0
        have : Kset n δ = ∅ := by
          subst hn0'
          ext x
          simp [Kset]
        rw [this] at hxKset
        exact hxKset
      have hxδ : p.2 ⟨0, hn⟩ ≥ δ := hxKset.1 ⟨0, hn⟩
      have hineq0 := hineq ⟨0, hn⟩
      have hmulvec : M.mulVec p.2 ⟨0, hn⟩ ≤ B := by
        calc M.mulVec p.2 ⟨0, hn⟩ = ∑ j, M ⟨0, hn⟩ j * p.2 j := rfl
          _ ≤ ∑ j, B * p.2 j := by apply Finset.sum_le_sum; intro j _; nlinarith [hB ⟨0, hn⟩ j, hxKset.1 j]
          _ = B * ∑ j, p.2 j := by rw [mul_sum]
          _ = B * 1 := by rw [hxKset.2]
          _ = B := mul_one B
      rw [le_div_iff₀ hδ]
      have hkey : p.1 * p.2 ⟨0, hn⟩ ≤ B := le_trans hineq0 hmulvec
      have hmul : p.1 * δ ≤ p.1 * p.2 ⟨0, hn⟩ := by nlinarith
      linarith
    -- [0, B/δ] × Kset n δ is compact
    have hcompact : IsCompact (Set.Icc 0 (B / δ) ×ˢ Kset n δ) :=
      isCompact_Icc.prod (isCompact_Kset n (le_of_lt hδ))
    -- Cset M δ is a closed subset, hence compact
    exact hcompact.of_isClosed_subset hclosed hsubset
  · -- Case B < 0: Cset M δ is empty
    have hempty : Cset M δ = ∅ := by
      by_cases hn : n = 0
      · subst hn
        ext ⟨t, x⟩
        simp [Cset, show (Kset 0 δ) = ∅ from by ext x; simp [Kset]]
      · ext ⟨t, x⟩
        simp only [Set.mem_empty_iff_false, iff_false]
        rw [Cset]
        simp only [Set.mem_setOf_eq]
        rintro ⟨ht, hxKset, hle⟩
        have hn' : 0 < n := Nat.pos_of_ne_zero hn
        have hxδ := hxKset.1 ⟨0, hn'⟩
        have hineq0 := hle ⟨0, hn'⟩
        have hmulvec : M.mulVec x ⟨0, hn'⟩ ≤ B := by
          calc M.mulVec x ⟨0, hn'⟩ = ∑ j, M ⟨0, hn'⟩ j * x j := rfl
            _ ≤ ∑ j, B * x j := by apply Finset.sum_le_sum; intro j _; nlinarith [hB ⟨0, hn'⟩ j, hxKset.1 j]
            _ = B * ∑ j, x j := by rw [mul_sum]
            _ = B * 1 := by rw [hxKset.2]
            _ = B := mul_one B
        nlinarith
    exact hempty ▸ isCompact_empty

