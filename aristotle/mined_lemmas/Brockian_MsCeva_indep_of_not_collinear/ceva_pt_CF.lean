import Mathlib
namespace Brockian.MsCeva

/-- Auxiliary: for three non-collinear points `A B C` of the plane, the vectors `B - A` and
`C - A` are linearly independent (stated in the concrete "no nontrivial relation" form). -/

lemma ceva_pt_CF (A B C : EuclideanSpace ℝ (Fin 2)) (u w s : ℝ)
    (hs2 : s * (1 - u) + s * u * w = w) :
    A + s • ((B + u • (C - B)) - A) = C + (1 - s * u) • ((A + w • (B - A)) - C) := by
  match_scalars <;> first | linear_combination hs2 | linear_combination -hs2 | ring

/-- Ceva's theorem (ratio form): if D,E,F lie on segments BC,CA,AB with parameters splitting
    them in ratios giving points D=B+u(C−B), E=C+v(A−C), F=A+w(B−A), then the cevians AD,BE,CF
    are concurrent iff (u/(1−u))·(v/(1−v))·(w/(1−w)) = 1.

    Note: a non-degeneracy hypothesis (`A`, `B`, `C` not collinear) has been added; without it
    the statement is false (e.g. `A = B = C` makes the left-hand side trivially true). -/
