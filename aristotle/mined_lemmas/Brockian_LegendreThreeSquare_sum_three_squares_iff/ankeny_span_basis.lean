import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

noncomputable def ankeny_span_basis (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Module.Basis (Fin 3) ℝ E3 :=
  let b0 : Module.Basis (Fin 3) ℝ E3 := Pi.basisFun ℝ (Fin 3)
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix n q b
  have hdet : A.det ≠ 0 := by
    -- The matrix is upper triangular with diagonal entries `n`, `2q`, `1`.
    -- (The `b`-entries do not affect the determinant.)
    have hA : A.det = (2 * n * q : ℝ) := by
      -- Explicit 3×3 determinant expansion.
      simp [A, ankeny_span_matrix, Matrix.det_fin_three]
      ring_nf
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    -- Show `2 * (n : ℝ) * (q : ℝ) ≠ 0` by contradiction.
    intro hzero
    have hmul : (2 : ℝ) * (n : ℝ) * (q : ℝ) = 0 := by
      -- rewrite the goal `A.det = 0` into `2*n*q = 0`
      -- (and normalize the multiplication order/associativity).
      have : (2 * n * q : ℝ) = 0 := by simpa [hA] using hzero
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have h' : (2 : ℝ) * (n : ℝ) = 0 ∨ (q : ℝ) = 0 := by
      -- reassociate to apply `mul_eq_zero`.
      have : ((2 : ℝ) * (n : ℝ)) * (q : ℝ) = 0 := by simpa [mul_assoc] using hmul
      exact mul_eq_zero.mp this
    cases h' with
    | inl h2n =>
        have : (2 : ℝ) = 0 ∨ (n : ℝ) = 0 := mul_eq_zero.mp h2n
        cases this with
        | inl h2 =>
            have : (2 : ℝ) ≠ 0 := by norm_num
            exact (this h2).elim
        | inr hn' => exact hn0 hn'
    | inr hq' =>
        exact hq0 hq'
  b0.map (Matrix.toLinearEquiv b0 A (isUnit_iff_ne_zero.mpr hdet))

