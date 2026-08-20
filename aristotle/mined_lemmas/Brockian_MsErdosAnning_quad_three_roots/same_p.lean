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

lemma same_p {A B C P Q q : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hq1 : ⟪q, B - A⟫ = dist P A - dist P B) (hq2 : ⟪q, C - A⟫ = dist P A - dist P C)
    (e1 : dist Q A - dist Q B = dist P A - dist P B)
    (e2 : dist Q A - dist Q C = dist P A - dist P C) :
    (P - A) - (dist P A) • q = (Q - A) - (dist Q A) • q := by
  -- Define r = (P - A) - (dist P A) • q - ((Q - A) - (dist Q A) • q)
  -- We show r is orthogonal to both (B - A) and (C - A)
  -- Since A, B, C are not collinear, r = 0
  set r := (P - A) - (dist P A) • q - ((Q - A) - (dist Q A) • q) with hr_def
  suffices h : r = 0 by rw [hr_def] at h; exact sub_eq_zero.mp h
  -- Show r is orthogonal to (B - A)
  have horthB : ⟪r, B - A⟫ = 0 := by
    simp only [hr_def]
    have hr_simp : (P - A - dist P A • q) - (Q - A - dist Q A • q) = (P - Q) - (dist P A - dist Q A) • q := by module
    rw [hr_simp]
    rw [inner_sub_left, inner_smul_left, hq1]
    have hPQ : P - Q = (P - A) - (Q - A) := by abel
    rw [hPQ, inner_sub_left]
    simp only [inner_formula]
    simp
    have he1' : dist Q A = dist Q B + (dist P A - dist P B) := by linarith
    rw [he1']
    ring
  -- Show r is orthogonal to (C - A)
  have horthC : ⟪r, C - A⟫ = 0 := by
    simp only [hr_def]
    have hr_simp : (P - A - dist P A • q) - (Q - A - dist Q A • q) = (P - Q) - (dist P A - dist Q A) • q := by module
    rw [hr_simp]
    rw [inner_sub_left, inner_smul_left, hq2]
    have hPQ : P - Q = (P - A) - (Q - A) := by abel
    rw [hPQ, inner_sub_left]
    simp only [inner_formula]
    simp
    have he2' : dist Q A = dist Q C + (dist P A - dist P C) := by linarith
    rw [he2']
    ring
  exact orth_eq_zero hABC horthB horthC

/-- If `‖p + x • q‖ = x` for three distinct values of `x`, then `p = 0` and `q` is a unit
vector. -/
