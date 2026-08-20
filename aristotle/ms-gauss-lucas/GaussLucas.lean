import Mathlib
namespace Brockian.MsGaussLucas
/-- The Gauss–Lucas theorem: every root of the derivative p' lies in the convex hull of the roots
    of p, for a nonconstant complex polynomial p. -/
theorem gauss_lucas (p : Polynomial ℂ) (hp : 0 < p.degree) (z : ℂ)
    (hz : p.derivative.IsRoot z) :
    z ∈ convexHull ℝ {w : ℂ | p.IsRoot w} := by
  sorry
end Brockian.MsGaussLucas
