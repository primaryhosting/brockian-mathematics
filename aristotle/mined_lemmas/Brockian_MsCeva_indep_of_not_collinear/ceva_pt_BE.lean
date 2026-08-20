import Mathlib
namespace Brockian.MsCeva

/-- Auxiliary: for three non-collinear points `A B C` of the plane, the vectors `B - A` and
`C - A` are linearly independent (stated in the concrete "no nontrivial relation" form). -/

lemma ceva_pt_BE (A B C : EuclideanSpace ℝ (Fin 2)) (u v s : ℝ)
    (hs : s * (u + (1 - u) * (1 - v)) = 1 - v) :
    A + s • ((B + u • (C - B)) - A) = B + (1 - s * (1 - u)) • ((C + v • (A - C)) - B) := by
  match_scalars <;> first | linear_combination hs | linear_combination -hs | ring

/-- Auxiliary: if `s * (1-u) + s * u * w = w`, then the point of the cevian `AD` with parameter
`s` also lies on the cevian `CF`. -/
