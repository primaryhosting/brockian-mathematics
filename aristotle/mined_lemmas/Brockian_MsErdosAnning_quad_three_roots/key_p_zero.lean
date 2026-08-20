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

lemma key_p_zero {a b c : ℝ} {p q : EuclideanSpace ℝ (Fin 2)} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hP : ‖p + a • q‖ = a) (hQ : ‖p + b • q‖ = b) (hR : ‖p + c • q‖ = c) :
    p = 0 ∧ ‖q‖ = 1 := by
  -- Squaring gives: ‖p‖² + 2x⟪p, q⟫ + x²‖q‖² = x²
  -- Rearranging: ‖p‖² + 2x⟪p, q⟫ + x²(‖q‖² - 1) = 0
  have ha_sq : ‖p‖^2 + 2 * a * ⟪p, q⟫ + a^2 * (‖q‖^2 - 1) = 0 := by
    have := congrArg (·^2) hP
    simp [norm_add_sq_real, norm_smul, mul_pow, sq_abs, inner_smul_right] at this
    linarith
  have hb_sq : ‖p‖^2 + 2 * b * ⟪p, q⟫ + b^2 * (‖q‖^2 - 1) = 0 := by
    have := congrArg (·^2) hQ
    simp [norm_add_sq_real, norm_smul, mul_pow, sq_abs, inner_smul_right] at this
    linarith
  have hc_sq : ‖p‖^2 + 2 * c * ⟪p, q⟫ + c^2 * (‖q‖^2 - 1) = 0 := by
    have := congrArg (·^2) hR
    simp [norm_add_sq_real, norm_smul, mul_pow, sq_abs, inner_smul_right] at this
    linarith
  -- Apply quad_three_roots with α = ‖q‖² - 1, β = 2⟪p, q⟫, γ = ‖p‖²
  have hcoeffs := quad_three_roots hab hac hbc
    (by linear_combination ha_sq : (‖q‖^2 - 1) * a^2 + 2 * ⟪p, q⟫ * a + ‖p‖^2 = 0)
    (by linear_combination hb_sq : (‖q‖^2 - 1) * b^2 + 2 * ⟪p, q⟫ * b + ‖p‖^2 = 0)
    (by linear_combination hc_sq : (‖q‖^2 - 1) * c^2 + 2 * ⟪p, q⟫ * c + ‖p‖^2 = 0)
  obtain ⟨hq2, _, hp2⟩ := hcoeffs
  exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp hp2), by
    have hqpos : 0 ≤ ‖q‖ := norm_nonneg q
    nlinarith [sq_nonneg ‖q‖]⟩

/-- Equality case of Cauchy-Schwarz: if `‖q‖ = 1`, `⟪q, w⟫ = k` and `‖w‖ ^ 2 = k ^ 2`,
then `w = k • q`. -/
