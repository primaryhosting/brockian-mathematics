import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_span_basis_q1_matrixOf (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Matrix.of (ankeny_span_basis_q1 n q b hn hq) = (ankeny_span_matrix_q1 n q b)ᵀ := by
  classical
  ext i j
  simp [ankeny_span_basis_q1, ankeny_span_matrix_q1, Module.Basis.map_apply, Matrix.toLinearEquiv, Matrix.of_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.transpose_apply]

