import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

noncomputable def ankeny_span_fundamentalDomain_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Set E3 :=
  ZSpan.fundamentalDomain (ankeny_span_basis_q1 n q b hn hq)

