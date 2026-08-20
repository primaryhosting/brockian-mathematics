import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

noncomputable def ankeny_span_basis_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Module.Basis (Fin 3) ℝ E3 :=
  let b0 : Module.Basis (Fin 3) ℝ E3 := Pi.basisFun ℝ (Fin 3)
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix_q1 n q b
  have hdet : A.det ≠ 0 := by
    have hA : A.det = (n * q : ℝ) := by
      simp [A, ankeny_span_matrix_q1, Matrix.det_fin_three]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    intro hzero
    have : (n * q : ℝ) = 0 := by simpa [hA] using hzero
    have hmul : (n : ℝ) = 0 ∨ (q : ℝ) = 0 := mul_eq_zero.mp this
    cases hmul with
    | inl hn' => exact hn0 hn'
    | inr hq' => exact hq0 hq'
  b0.map (Matrix.toLinearEquiv b0 A (isUnit_iff_ne_zero.mpr hdet))

