import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_span_isAddFundamentalDomain (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    IsAddFundamentalDomain (ankeny_span_lattice n q b hn hq)
      (ankeny_span_fundamentalDomain n q b hn hq) volume := by
  simpa [ankeny_span_lattice, ankeny_span_fundamentalDomain] using
    (ZSpan.isAddFundamentalDomain' (ankeny_span_basis n q b hn hq) volume)

