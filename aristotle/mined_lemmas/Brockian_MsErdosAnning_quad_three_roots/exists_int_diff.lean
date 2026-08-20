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

lemma exists_int_diff {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, dist x y = n) {x A B : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ S) (hA : A ∈ S) (hB : B ∈ S) : ∃ k : ℤ, dist x A - dist x B = (k : ℝ) := by
  obtain ⟨na, hna⟩ := hint x hx A hA
  obtain ⟨nb, hnb⟩ := hint x hx B hB
  exact ⟨na - nb, by simp [hna, hnb]⟩

/-- A point collinear with two distinct points lies on the line through them. -/
