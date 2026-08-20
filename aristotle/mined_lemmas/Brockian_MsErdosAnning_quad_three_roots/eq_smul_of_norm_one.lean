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

lemma eq_smul_of_norm_one {q w : EuclideanSpace ℝ (Fin 2)} {k : ℝ} (hq : ‖q‖ = 1)
    (h : ⟪q, w⟫ = k) (hw : ‖w‖ ^ 2 = k ^ 2) : w = k • q := by
  have hinner_symm : ⟪w, q⟫ = k := by rw [← real_inner_comm]; exact h
  have hnorm_km_sq : ‖k • q‖ ^ 2 = k ^ 2 := by
    rw [norm_smul, hq, Real.norm_eq_abs]
    simp
  have hnorm_sq : ‖w - k • q‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, inner_smul_right, hinner_symm, hw, hnorm_km_sq]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_sq))

/-! ### The key finiteness step -/

/-- Three distinct points cannot have the same pair of distance differences to two of the
vertices of a non-degenerate triangle. -/
