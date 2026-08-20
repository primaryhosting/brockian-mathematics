import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_span_volume_fundamentalDomain_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    volume (ankeny_span_fundamentalDomain_q1 n q b hn hq) = (n * q : ℝ≥0∞) := by
  classical
  let B : Module.Basis (Fin 3) ℝ E3 := ankeny_span_basis_q1 n q b hn hq
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix_q1 n q b
  have hvol :
      volume (ankeny_span_fundamentalDomain_q1 n q b hn hq) =
        ENNReal.ofReal |(Matrix.of B).det| := by
    simpa [ankeny_span_fundamentalDomain_q1, B] using (ZSpan.volume_fundamentalDomain B)
  have hB : Matrix.of B = Aᵀ := by
    simpa [A, B] using (ankeny_span_basis_q1_matrixOf n q b hn hq)
  have hdetA : A.det = (n * q : ℝ) := by
    simp [A, ankeny_span_matrix_q1, Matrix.det_fin_three]
  have hdetB : (Matrix.of B).det = (n * q : ℝ) := by
    calc
      (Matrix.of B).det = (Aᵀ).det := by simp [hB]
      _ = A.det := by simpa using (Matrix.det_transpose A)
      _ = (n * q : ℝ) := hdetA
  have hnonneg : 0 ≤ (n * q : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.zero_le q)
    nlinarith
  calc
    volume (ankeny_span_fundamentalDomain_q1 n q b hn hq)
        = ENNReal.ofReal |(Matrix.of B).det| := hvol
    _ = ENNReal.ofReal (n * q : ℝ) := by simp [hdetB, abs_of_nonneg hnonneg]
    _ = (n * q : ℝ≥0∞) := by simp [ENNReal.ofReal_natCast]

/-!
## Q₁ Minkowski setup (smaller radius, same diagonal map)

For the Q₁ route we keep the same diagonal map `diag(√(2q), 1, √n)` but shrink the ball radius to
\[
r = \sqrt{2 n q},
\]
so that membership gives the *stronger* upper bound `2q x^2 + y^2 + n z^2 < 2 n q`.

This is the key trick that lets us pin down a multiple of `n*q` to be *exactly* `n*q`.
-/

private noncomputable def ankenyBallRadius_q1 (n q : ℝ) : ℝ :=
  Real.sqrt (2 * (n * q))

private noncomputable def ankenyEllipsoidL2_q1 (n q : ℝ) : Set E3 :=
  GeometryOfNumbers.Minkowski.ankenyDiagMap n q ⁻¹' l2Ball (ankenyBallRadius_q1 n q)

