import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

noncomputable def ankeny_span_matrix_q1 (n q : ℕ) (b : ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(n : ℝ), (q : ℝ), (b : ℝ);
    0, (q : ℝ), (b : ℝ);
    0, 0, (1 : ℝ)]

