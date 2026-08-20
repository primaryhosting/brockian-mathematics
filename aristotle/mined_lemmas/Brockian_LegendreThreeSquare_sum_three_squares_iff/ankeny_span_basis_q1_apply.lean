import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_span_basis_q1_apply (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) (i j : Fin 3) :
    ankeny_span_basis_q1 n q b hn hq i j = ankeny_span_matrix_q1 n q b j i := by
  have hM := ankeny_span_basis_q1_matrixOf n q b hn hq
  have := congrArg (fun M => M i j) hM
  simpa [Matrix.of_apply, Matrix.transpose_apply] using this

