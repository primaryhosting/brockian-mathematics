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

lemma collinear_of_smul_eq {A B C : EuclideanSpace ℝ (Fin 2)} {s t : ℝ}
    (hst : ¬ (s = 0 ∧ t = 0)) (h : s • (B - A) = t • (C - A)) :
    Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
  by_cases hs : s = 0
  · -- If s = 0, then t ≠ 0, so C = A
    have ht : t ≠ 0 := fun ht => hst ⟨hs, ht⟩
    have hC : C = A := by
      have : t • (C - A) = 0 := by rw [← h, hs, zero_smul]
      exact sub_eq_zero.mp (smul_eq_zero.mp this |>.resolve_left ht)
    simp [hC, collinear_pair]
  · by_cases ht : t = 0
    · -- If t = 0, then s ≠ 0, so B = A
      have hB : B = A := by
        have : s • (B - A) = 0 := by rw [h, ht, zero_smul]
        exact sub_eq_zero.mp (smul_eq_zero.mp this |>.resolve_left hs)
      simp [hB, collinear_pair]
    · -- Both s ≠ 0 and t ≠ 0
      have hBA : B - A = (t / s) • (C - A) := by
        have h1 : s • (B - A) = s • ((t / s) • (C - A)) := by
          rw [h, smul_smul]
          congr 1
          field_simp
        exact smul_right_injective (M := EuclideanSpace ℝ (Fin 2)) hs h1
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      use A, C - A
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨t / s, by rw [← hBA]; simp⟩
      · exact ⟨1, by simp⟩

/-- If `A`, `B`, `C` are not collinear, a vector orthogonal to `B - A` and `C - A` vanishes. -/
