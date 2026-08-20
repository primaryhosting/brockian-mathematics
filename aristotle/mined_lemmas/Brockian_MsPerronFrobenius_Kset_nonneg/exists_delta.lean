import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

lemma exists_delta (hn : 0 < n) (hpos : ∀ i j, 0 < M i j) :
    ∃ δ B : ℝ, 0 < δ ∧ δ ≤ (n : ℝ)⁻¹ ∧ (∀ i j, M i j ≤ B) ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
        (fun i => M.mulVec x i / ∑ j, M.mulVec x j) ∈ Kset n δ := by
  -- Let's pick δ small enough and B large enough
  let minM := sInf (Set.range (fun p : Fin n × Fin n => M p.1 p.2))
  let maxM := sSup (Set.range (fun p : Fin n × Fin n => M p.1 p.2))
  -- The set of matrix entries is finite and nonempty
  have hne : Set.Nonempty (Set.range (fun p : Fin n × Fin n => M p.1 p.2)) :=
    ⟨M ⟨0, hn⟩ ⟨0, hn⟩, ⟨(⟨0, hn⟩, ⟨0, hn⟩), rfl⟩⟩
  have hfin : Set.Finite (Set.range (fun p : Fin n × Fin n => M p.1 p.2)) := Set.finite_range _
  -- minM > 0 since all entries are positive
  have hminM_pos : 0 < minM := by
    have hbound : ∀ y ∈ Set.range (fun p : Fin n × Fin n => M p.1 p.2), 0 < y := by
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact hpos i j
    -- Use a Finset and inf'
    let s := Finset.image (fun p : Fin n × Fin n => M p.1 p.2) Finset.univ
    have hs_eq : (s : Set ℝ) = Set.range (fun p : Fin n × Fin n => M p.1 p.2) := by
      ext y; simp [s]
    have hs_nonempty : s.Nonempty := ⟨M ⟨0, hn⟩ ⟨0, hn⟩, by simp [s]⟩
    have h_eq : minM = s.min' hs_nonempty := by
      simp only [minM]
      apply le_antisymm
      · apply csInf_le hfin.bddBelow
        exact hs_eq ▸ Finset.min'_mem _ _
      · exact le_csInf hne (fun y hy => by
          have hy' : y ∈ s := hs_eq.symm.subset hy
          exact Finset.min'_le _ _ hy')
    rw [h_eq]
    have hmin'_mem : s.min' hs_nonempty ∈ s := Finset.min'_mem _ _
    rw [Finset.mem_image] at hmin'_mem
    obtain ⟨⟨i, j⟩, _, h_eq2⟩ := hmin'_mem
    rw [← h_eq2]
    exact hbound _ ⟨⟨i, j⟩, rfl⟩
  -- maxM bounds all entries
  have hmaxM_ub : ∀ i j, M i j ≤ maxM := by
    intro i j
    exact le_csSup (hfin.bddAbove) ⟨(i, j), rfl⟩
  have hmaxM_pos : 0 < maxM := by
    have hmem : M ⟨0, hn⟩ ⟨0, hn⟩ ∈ Set.range (fun p : Fin n × Fin n => M p.1 p.2) := ⟨(⟨0, hn⟩, ⟨0, hn⟩), rfl⟩
    have : 0 < M ⟨0, hn⟩ ⟨0, hn⟩ := hpos ⟨0, hn⟩ ⟨0, hn⟩
    exact lt_of_lt_of_le this (le_csSup (hfin.bddAbove) hmem)
  -- Choose B = maxM
  use minM / ((n : ℝ) * maxM)
  use maxM
  refine ⟨?_, ?_, hmaxM_ub, ?_⟩
  · -- Show 0 < minM / (n * maxM)
    positivity
  · -- Show minM / (n * maxM) ≤ n⁻¹
    have h1 : minM ≤ maxM := by
      have hmem : M ⟨0, hn⟩ ⟨0, hn⟩ ∈ Set.range (fun p : Fin n × Fin n => M p.1 p.2) := ⟨(⟨0, hn⟩, ⟨0, hn⟩), rfl⟩
      exact le_trans (csInf_le hfin.bddBelow hmem) (le_csSup hfin.bddAbove hmem)
    calc minM / ((n : ℝ) * maxM) ≤ maxM / ((n : ℝ) * maxM) := by gcongr
      _ = (n : ℝ)⁻¹ := by field_simp
  · -- Show the normalized image is in Kset n δ
    intro x hx_nonneg hx_sum
    have hsum_pos : 0 < ∑ j, M.mulVec x j := by
      -- Since ∑ x = 1, there exists some k with x k > 0
      obtain ⟨k, hk⟩ : ∃ k, 0 < x k := by
        by_contra h
        push_neg at h
        have : ∑ i, x i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
        linarith
      -- For any j, (M *ᵥ x) j ≥ M j k * x k > 0
      have hge : ∀ j, M.mulVec x j ≥ M j k * x k := by
        intro j
        simp [Matrix.mulVec]
        apply Finset.single_le_sum (fun i _ => mul_nonneg (le_of_lt (hpos j i)) (hx_nonneg i))
        simp
      have hpos_jk : 0 < M ⟨0, hn⟩ k * x k := mul_pos (hpos _ _) hk
      have hnonneg : ∀ j, 0 ≤ M.mulVec x j := fun j => by
        simp [Matrix.mulVec]
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg (le_of_lt (hpos j i)) (hx_nonneg i)
      calc 0 < M (⟨0, hn⟩ : Fin n) k * x k := hpos_jk
        _ ≤ M.mulVec x (⟨0, hn⟩ : Fin n) := hge (⟨0, hn⟩ : Fin n)
        _ ≤ ∑ j, M.mulVec x j := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    constructor
    · -- Each coordinate ≥ δ
      intro i
      -- (M *ᵥ x) i ≥ minM
      have hnum : M.mulVec x i ≥ minM := by
        simp [Matrix.mulVec]
        calc minM = minM * ∑ j, x j := by rw [hx_sum, mul_one]
          _ = ∑ j, minM * x j := by rw [Finset.mul_sum]
          _ ≤ ∑ j, M i j * x j := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_right (csInf_le hfin.bddBelow ⟨(i, j), rfl⟩) (hx_nonneg j)
      -- ∑ j, (M *ᵥ x) j ≤ n * maxM
      have hdenom : ∑ j, M.mulVec x j ≤ (n : ℝ) * maxM := by
        simp only [Matrix.mulVec, dotProduct]
        calc ∑ j, ∑ k, M j k * x k ≤ ∑ j, ∑ k, maxM * x k := by
              apply Finset.sum_le_sum
              intro j _
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_right (hmaxM_ub j k) (hx_nonneg k)
          _ = ∑ _j : Fin n, maxM * 1 := by
              congr 1
              ext j
              rw [← Finset.mul_sum, hx_sum, mul_one]
          _ = n * maxM := by simp [mul_comm]
      -- So ratio ≥ minM / (n * maxM) = δ
      have hxi_nonneg : 0 ≤ (M *ᵥ x) i := by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (hpos i j).le (hx_nonneg j)
      have hnpos : (0:ℝ) < (n : ℝ) * maxM := by positivity
      calc minM / ((n : ℝ) * maxM)
          ≤ (M *ᵥ x) i / ((n : ℝ) * maxM) := by gcongr
        _ ≤ (M *ᵥ x) i / (∑ j, M.mulVec x j) := by gcongr
    · -- Sum equals 1
      rw [← Finset.sum_div]
      rw [div_self (ne_of_gt hsum_pos)]

