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

lemma finite_of_no_three {X : Type*} (T : Set X)
    (h : ∀ P ∈ T, ∀ Q ∈ T, ∀ R ∈ T, P ≠ Q → P ≠ R → Q ≠ R → False) : T.Finite := by
  by_contra hinf
  -- T is infinite, so we can find 3 distinct elements
  have : ∃ a b c : _, a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    let f := Set.Infinite.natEmbedding T hinf
    have h0 := (f 0).2
    have h1 := (f 1).2
    have h2 := (f 2).2
    exact ⟨(f 0 : X), (f 1 : X), (f 2 : X), h0, h1, h2, Subtype.coe_injective.ne (f.injective.ne (by norm_num : (0 : ℕ) ≠ 1)), Subtype.coe_injective.ne (f.injective.ne (by norm_num : (0 : ℕ) ≠ 2)), Subtype.coe_injective.ne (f.injective.ne (by norm_num : (1 : ℕ) ≠ 2))⟩
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := this
  exact h a ha b hb c hc hab hac hbc

/-! ### Plane geometry lemmas -/

/-- In the plane, a vector orthogonal to two vectors which are not parallel is zero. -/
