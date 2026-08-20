import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_span_volume_fundamentalDomain (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    volume (ankeny_span_fundamentalDomain n q b hn hq) = (2 * n * q : ℝ≥0∞) := by
  classical
  let B : Module.Basis (Fin 3) ℝ E3 := ankeny_span_basis n q b hn hq
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix n q b
  have hvol :
      volume (ankeny_span_fundamentalDomain n q b hn hq) =
        ENNReal.ofReal |(Matrix.of B).det| := by
    simpa [ankeny_span_fundamentalDomain, B] using (ZSpan.volume_fundamentalDomain B)
  have hB : Matrix.of B = Aᵀ := by
    simpa [A, B] using (ankeny_span_basis_matrixOf n q b hn hq)
  have hdetA : A.det = (2 * n * q : ℝ) := by
    simp [A, ankeny_span_matrix, Matrix.det_fin_three]
    ring_nf
  have hdetB : (Matrix.of B).det = (2 * n * q : ℝ) := by
    calc
      (Matrix.of B).det = (Aᵀ).det := by simp [hB]
      _ = A.det := by simpa using (Matrix.det_transpose A)
      _ = (2 * n * q : ℝ) := hdetA
  have hnonneg : 0 ≤ (2 * n * q : ℝ) := by
    nlinarith
  -- Convert `ENNReal.ofReal |det|` to an `ℝ≥0∞` nat-cast.
  calc
    volume (ankeny_span_fundamentalDomain n q b hn hq)
        = ENNReal.ofReal |(Matrix.of B).det| := hvol
    _ = ENNReal.ofReal (2 * n * q : ℝ) := by simp [hdetB, abs_of_nonneg hnonneg]
    _ = (2 * n * q : ℝ≥0∞) := by simp [ENNReal.ofReal_natCast]

/-!
### Q₁-variant explicit covolume kernel (modulus `q`, covolume `n*q`)

For the `Q₁ = qx² + y² + nz²` route we want the same “explicit span lattice” trick, but with
the `2q` column replaced by `q`. The determinant becomes `n*q`.
-/

/-- Q₁-variant span matrix (replace `2q` by `q`), with `det = n*q`. -/
