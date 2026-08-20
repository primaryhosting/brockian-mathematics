import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

lemma exists_improve (hn : 0 < n) (hpos : ∀ i j, 0 < M i j) {δ : ℝ} (hδ : 0 < δ)
    (hnorm : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
        (fun i => M.mulVec x i / ∑ j, M.mulVec x j) ∈ Kset n δ)
    {r : ℝ} {v : Fin n → ℝ} (hv : v ∈ Kset n δ)
    (hineq : ∀ i, r * v i ≤ M.mulVec v i) (hne : M.mulVec v ≠ r • v) :
    ∃ ε > 0, ∃ u ∈ Kset n δ, ∀ i, (r + ε) * u i ≤ M.mulVec u i := by
  -- v has all positive entries since v ∈ Kset n δ and δ > 0
  have hvpos : ∀ i, 0 < v i := fun i => lt_of_lt_of_le hδ (hv.1 i)
  -- Since M.mulVec v ≠ r • v and M.mulVec v ≥ r • v, there's a strict inequality somewhere
  have hstrict : ∃ i, r * v i < M.mulVec v i := by
    by_contra h
    push_neg at h
    exact hne (funext (fun i => le_antisymm (h i) (hineq i)))
  -- v ≠ 0
  have hv0 : v ≠ 0 := Kset_ne_zero hv
  -- M.mulVec v has all positive entries
  have hMvpos : ∀ i, 0 < M.mulVec v i := mulVec_pos hpos (fun i => le_of_lt (hvpos i)) hv0
  -- Define S = ∑ j, M.mulVec v j, which is positive
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set S := ∑ j, M.mulVec v j with hSdef
  have hSpos : 0 < S := Finset.sum_pos (fun _ _ => hMvpos _) Finset.univ_nonempty
  -- The normalized image w is in Kset n δ (using hnorm with v)
  have hwK : (fun i => M.mulVec v i / S) ∈ Kset n δ := hnorm v (fun i => le_of_lt (hvpos i)) hv.2
  -- M.mulVec (M.mulVec v) > r * M.mulVec v componentwise (strictly)
  have hM2v_strict_all : ∀ i, r * M.mulVec v i < M.mulVec (M.mulVec v) i := by
    intro i
    have hMv_i_pos := hMvpos i
    obtain ⟨k', hk'⟩ := hstrict
    have hSum_ge : ∑ j, M i j * M.mulVec v j > ∑ j, M i j * (r * v j) := by
      apply Finset.sum_lt_sum
      · intro j _
        apply mul_le_mul_of_nonneg_left (hineq j) (le_of_lt (hpos i j))
      · exact ⟨k', Finset.mem_univ k', mul_lt_mul_of_pos_left hk' (hpos i k')⟩
    have hSum_eq : ∑ j, M i j * (r * v j) = r * M.mulVec v i := by
      rw [Matrix.mulVec, dotProduct]
      have : ∑ j, M i j * (r * v j) = ∑ j, r * (M i j * v j) := by
        congr 1 with j; ring
      rw [this, ← Finset.mul_sum]
    have hM2v_i : M.mulVec (M.mulVec v) i = ∑ j, M i j * M.mulVec v j := rfl
    linarith
  -- Use exists_eps_gap to get uniform ε
  obtain ⟨ε, hεpos, hε⟩ := exists_eps_gap hn hMvpos hM2v_strict_all
  -- Now show (r + ε) * w i ≤ M.mulVec w i for w = M.mulVec v / S
  refine ⟨ε, hεpos, fun i => M.mulVec v i / S, hwK, ?_⟩
  intro i
  calc (r + ε) * (M.mulVec v i / S)
      = ((r + ε) * M.mulVec v i) / S := by ring
    _ ≤ (M.mulVec (M.mulVec v) i) / S := by gcongr; exact hε i
    _ = M.mulVec (fun j => M.mulVec v j / S) i := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_div]
        congr 1 with j
        rw [mul_div_assoc]

/-- Perron's theorem (positive case): a square matrix with strictly positive real entries has a
    positive real eigenvalue with a strictly positive eigenvector. -/
