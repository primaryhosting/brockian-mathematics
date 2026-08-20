import Mathlib

/-!
# The Erdős–Anning theorem

An infinite set of points in the Euclidean plane whose pairwise distances are all integers
must be collinear.

## Proof outline

Assume `S` is infinite with integral pairwise distances and pick `A ≠ B` in `S`.  If some
`C ∈ S` is off the line `AB`, then `A`, `B`, `C` form a non-degenerate triangle.  For every
`P ∈ S` the two differences `dist P A - dist P B` and `dist P A - dist P C` are integers
bounded in absolute value by `dist A B` and `dist A C` respectively, so only finitely many
pairs of values occur (`finite_of_not_collinear`).  The heart of the argument (`key`) shows
that three *distinct* points cannot share the same pair of differences: writing
`⟪P - A, B - A⟫` in terms of the distances (`inner_formula`) shows that all such points lie
on a common line `A + p + x • q` with `x = dist P A`, and `‖p + x • q‖ = x` can hold for at
most two values of `x` unless `p = 0` and `‖q‖ = 1` (`key_p_zero`), in which case `B - A`
and `C - A` are both multiples of `q`, contradicting non-collinearity.  Hence `S` would be
finite, a contradiction.
-/

namespace Brockian.MsErdosAnning

open scoped RealInnerProductSpace

/-! ### Auxiliary algebraic lemmas -/

/-- A real quadratic with three distinct roots is identically zero. -/

lemma orth_eq_zero {A B C : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    {u : EuclideanSpace ℝ (Fin 2)} (h1 : ⟪u, B - A⟫ = 0) (h2 : ⟪u, C - A⟫ = 0) : u = 0 := by
  by_contra hu
  obtain ⟨s, t, hst, h⟩ := dep_of_orth hu h1 h2
  exact hABC (collinear_of_smul_eq hst h)

/-- If `A`, `B`, `C` are not collinear, then prescribed inner products with `B - A` and `C - A`
are realized by some vector. -/
