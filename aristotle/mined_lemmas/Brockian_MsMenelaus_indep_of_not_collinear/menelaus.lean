import Mathlib
namespace Brockian.MsMenelaus

/-- If `A`, `B`, `C` are not collinear, then `B - A` and `C - A` are linearly independent,
stated concretely as: any vanishing linear combination has zero coefficients. -/

theorem menelaus (A B C : EuclideanSpace ℝ (Fin 2)) (u v w : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hu : u ≠ 1) (hv : v ≠ 1) (hw : w ≠ 1)
    (D E F : EuclideanSpace ℝ (Fin 2))
    (hD : D = B + u • (C - B)) (hE : E = C + v • (A - C)) (hF : F = A + w • (B - A)) :
    Collinear ℝ ({D, E, F} : Set (EuclideanSpace ℝ (Fin 2)))
      ↔ (u / (1 - u)) * (v / (1 - v)) * (w / (1 - w)) = -1 := by
  have hbc := indep_of_not_collinear A B C hABC
  have hu' : (1 : ℝ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hv' : (1 : ℝ) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have hw' : (1 : ℝ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hDc : D = A + (1 - u) • (B - A) + u • (C - A) := by
    rw [hD]; module
  have hEc : E = A + (0 : ℝ) • (B - A) + (1 - v) • (C - A) := by
    rw [hE]; module
  have hFc : F = A + w • (B - A) + (0 : ℝ) • (C - A) := by
    rw [hF]; module
  have hprod : (1 - u) * (1 - v) * (1 - w) ≠ 0 := mul_ne_zero (mul_ne_zero hu' hv') hw'
  rw [hDc, hEc, hFc, collinear_triple_iff (B - A) (C - A) hbc,
    div_mul_div_comm, div_mul_div_comm, div_eq_iff hprod]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

end Brockian.MsMenelaus

