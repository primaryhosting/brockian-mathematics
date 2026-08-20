import Mathlib
namespace Brockian.MasonStothers
/-- Mason–Stothers (polynomial abc): for coprime polynomials with a + b = c, not all constant,
    max(deg a, deg b, deg c) < number of distinct roots of a·b·c. -/
theorem mason_stothers {K : Type*} [Field K] (a b c : Polynomial K)
    (hab : IsCoprime a b) (hsum : a + b = c) (hnc : ¬ (a.natDegree = 0 ∧ b.natDegree = 0))
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    max (max a.natDegree b.natDegree) c.natDegree <
      (a * b * c).roots.toFinset.card := by
  sorry
end Brockian.MasonStothers
