import Mathlib
namespace Brockian.MsCeva

/-- Auxiliary: for three non-collinear points `A B C` of the plane, the vectors `B - A` and
`C - A` are linearly independent (stated in the concrete "no nontrivial relation" form). -/

lemma ceva_alg_forward {u v w s t r : ℝ}
    (e1 : s * (1 - u) = 1 - t) (e2 : s * u = t * (1 - v))
    (e3 : s * (1 - u) = r * w) (e4 : s * u = 1 - r) :
    u * v * w = (1 - u) * (1 - v) * (1 - w) := by
  linear_combination ((1 - u) + u * w) * e2 + ((1 - u) + u * w) * (1 - v) * e1
    - (u + (1 - u) * (1 - v)) * e3 - (u + (1 - u) * (1 - v)) * w * e4

/-- Auxiliary: if `s` is the parameter with `s * (u + (1-u)(1-v)) = 1 - v`, then the point of the
cevian `AD` with parameter `s` also lies on the cevian `BE`. -/
