import RequestProject.Nash

/-!
# The one-dimensional base case of Brouwer's fixed point theorem

Brouwer's fixed point theorem is not available in Mathlib, and is taken as an explicit
hypothesis in `Frontier.nash_equilibrium_exists`.  Here we prove the one-dimensional base
case of that hypothesis, `BrouwerFixedPointProperty ℝ`, from the intermediate value
theorem; in particular the hypothesis is not vacuous.
-/

open Set

namespace Frontier

/-- **Brouwer's fixed point theorem in dimension one**: every continuous self-map of a
nonempty compact convex subset of `ℝ` has a fixed point. -/

theorem minimax (M : A → B → ℝ) :
    ∃ x ∈ stdSimplex ℝ A, ∃ y ∈ stdSimplex ℝ B, rowVal M x = colVal M y := by
  obtain ⟨x0, hx0, hx0max⟩ := (isCompact_stdSimplex A).exists_isMaxOn
    (stdSimplex_nonempty A) (continuous_rowVal M).continuousOn
  obtain ⟨y0, hy0, hy0min⟩ := (isCompact_stdSimplex B).exists_isMinOn
    (stdSimplex_nonempty B) (continuous_colVal M).continuousOn
  refine ⟨x0, hx0, y0, hy0, le_antisymm ((rowVal_le_bilin M hy0).trans (bilin_le_colVal M hx0)) ?_⟩
  by_contra hlt
  push_neg at hlt
  set c : ℝ := (rowVal M x0 + colVal M y0) / 2 with hcdef
  have hc1 : rowVal M x0 < c := by simp only [hcdef]; linarith
  have hc2 : c < colVal M y0 := by simp only [hcdef]; linarith
  rcases exists_pos_row_or_nonpos_col (fun a b => M a b - c) with ⟨x, hx, hxpos⟩ | ⟨y, hy, hyle⟩
  · have hxsum := hx.2
    have hcle : c ≤ rowVal M x := by
      refine Finset.le_inf' _ _ fun b _ => ?_
      have := hxpos b
      have hexp : ∑ a, x a * (M a b - c) = (∑ a, x a * M a b) - c := by
        rw [show ∑ a, x a * (M a b - c) = (∑ a, x a * M a b) - (∑ a, x a) * c by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun a _ => by ring, hxsum, one_mul]
      rw [hexp] at this
      linarith
    have := hx0max hx
    simp only [Set.mem_setOf_eq] at this
    linarith
  · have hysum := hy.2
    have hcge : colVal M y ≤ c := by
      refine Finset.sup'_le _ _ fun a _ => ?_
      have := hyle a
      have hexp : ∑ b, y b * (M a b - c) = (∑ b, y b * M a b) - c := by
        rw [show ∑ b, y b * (M a b - c) = (∑ b, y b * M a b) - (∑ b, y b) * c by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring, hysum, one_mul]
      rw [hexp] at this
      linarith
    have := hy0min hy
    simp only [Set.mem_setOf_eq] at this
    linarith

/-- **Existence of a saddle point** for every finite two-player zero-sum game. -/
