import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma exists_large_degree_of_eigenvector {n : ℕ} (H : Finset (Q n)) (c : ℝ)
    (hc : |c| = Real.sqrt n) (y : Q n → ℝ) (hy : y ≠ 0)
    (hAy : sgnAdj *ᵥ y = c • y) (hsupp : ∀ v, v ∉ H → y v = 0) :
    ∃ v ∈ H, Real.sqrt n ≤ (degIn H v : ℝ) := by
  obtain ⟨v, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Q n)) (fun v => |y v|)
    ⟨fun _ => false, Finset.mem_univ _⟩
  have hmax' : ∀ u, |y u| ≤ |y v| := fun u => hmax u (Finset.mem_univ u)
  have hyv : 0 < |y v| := by
    obtain ⟨u, hu⟩ := Function.ne_iff.1 hy
    exact lt_of_lt_of_le (abs_pos.2 hu) (hmax' u)
  have hvH : v ∈ H := by
    by_contra hv
    rw [hsupp v hv] at hyv
    simp at hyv
  refine ⟨v, hvH, ?_⟩
  set S := H.filter (fun u => adj u v) with hS
  have hrow : ∑ u : Q n, sgnAdj v u * y u = c * y v := by
    have h := congrFun hAy v
    simpa [Matrix.mulVec, dotProduct] using h
  have hsum : ∑ u : Q n, sgnAdj v u * y u = ∑ u ∈ S, sgnAdj v u * y u := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro u _ hu
    rw [hS] at hu
    simp only [Finset.mem_filter, not_and] at hu
    by_cases hH' : u ∈ H
    · have hnadj : ¬ adj u v := hu hH'
      have h0 : sgnAdj v u = 0 := by
        by_contra h0
        exact hnadj (adj_of_sgnAdj_ne_zero h0)
      rw [h0, zero_mul]
    · rw [hsupp u hH', mul_zero]
  have hbound : |c| * |y v| ≤ (S.card : ℝ) * |y v| := by
    calc |c| * |y v| = |c * y v| := (abs_mul _ _).symm
    _ = |∑ u ∈ S, sgnAdj v u * y u| := by rw [← hsum, hrow]
    _ ≤ ∑ u ∈ S, |sgnAdj v u * y u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ S, 1 * |y v| := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_sgnAdj_le_one v u) (hmax' u) (abs_nonneg _) zero_le_one
    _ = (S.card : ℝ) * |y v| := by rw [Finset.sum_const, nsmul_eq_mul, one_mul]
  rw [hc] at hbound
  have hfin := le_of_mul_le_mul_right
    (by linarith [hbound] : Real.sqrt n * |y v| ≤ (S.card : ℝ) * |y v|) hyv
  simpa [degIn, hS] using hfin

/-- Huang's Sensitivity Theorem (2019): every induced subgraph of the n-cube on more
    than half of its `2^n` vertices contains a vertex of degree at least `√n`. -/
