import Mathlib
namespace Brockian.MsGaussLucas

open Polynomial

/-- The conjugate of `u⁻¹` is the positive real multiple `(normSq u)⁻¹` of `u`. -/

theorem gauss_lucas (p : Polynomial ℂ) (hp : 0 < p.degree) (z : ℂ)
    (hz : p.derivative.IsRoot z) :
    z ∈ convexHull ℝ {w : ℂ | p.IsRoot w} := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  by_cases hpz : p.IsRoot z
  · exact subset_convexHull ℝ _ hpz
  · obtain ⟨a, r, ha, hfac⟩ := exists_linear_factorization p hp0
    have hn : 0 < p.natDegree := natDegree_pos_iff_degree_pos.mpr hp
    have hne : ∀ i, z ≠ r i := by
      intro i hi
      apply hpz
      rw [hfac]
      simp only [IsRoot, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; ring)]
      ring
    have hsum := sum_inv_eq_zero_of_isRoot_derivative p a ha r hfac z hz hpz
    have hmem := mem_convexHull_of_sum_inv_eq_zero hn r z hne hsum
    refine convexHull_mono ?_ hmem
    rintro w ⟨i, rfl⟩
    show p.IsRoot (r i)
    rw [hfac]
    simp only [IsRoot, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by ring)]
    ring

end Brockian.MsGaussLucas

