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

lemma quad_three_roots {α β γ a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : α * a ^ 2 + β * a + γ = 0) (hb : α * b ^ 2 + β * b + γ = 0)
    (hc : α * c ^ 2 + β * c + γ = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  -- Subtract pairs of equations to eliminate γ
  have hsub1 : α * (a ^ 2 - b ^ 2) + β * (a - b) = 0 := by linarith
  have hsub2 : α * (a ^ 2 - c ^ 2) + β * (a - c) = 0 := by linarith
  have hsub3 : α * (b ^ 2 - c ^ 2) + β * (b - c) = 0 := by linarith
  -- Factor: (a² - b²) = (a - b)(a + b)
  have hfact1 : (a - b) * (α * (a + b) + β) = 0 := by ring_nf; linarith
  have hfact2 : (a - c) * (α * (a + c) + β) = 0 := by ring_nf; linarith
  have hfact3 : (b - c) * (α * (b + c) + β) = 0 := by ring_nf; linarith
  -- Since a ≠ b, a ≠ c, b ≠ c, we get the linear equations
  have h1 : α * (a + b) + β = 0 := (mul_eq_zero.mp hfact1).resolve_left (sub_ne_zero.mpr hab)
  have h2 : α * (a + c) + β = 0 := (mul_eq_zero.mp hfact2).resolve_left (sub_ne_zero.mpr hac)
  have h3 : α * (b + c) + β = 0 := (mul_eq_zero.mp hfact3).resolve_left (sub_ne_zero.mpr hbc)
  -- From h1 and h2: α * (b - c) = 0, so α = 0
  have hα : α = 0 := by
    have : α * (b - c) = 0 := by linarith
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero (sub_ne_zero.mpr hbc) this
  -- With α = 0, h1 gives β = 0
  have hβ : β = 0 := by simp [hα] at h1; linarith
  -- With α = 0 and β = 0, ha gives γ = 0
  have hγ : γ = 0 := by simp [hα, hβ] at ha; linarith
  exact ⟨hα, hβ, hγ⟩

/-- A set in which no three elements are pairwise distinct is finite. -/
