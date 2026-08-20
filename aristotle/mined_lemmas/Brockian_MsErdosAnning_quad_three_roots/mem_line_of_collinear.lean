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

lemma mem_line_of_collinear {A B x : EuclideanSpace ℝ (Fin 2)} (hAB : A ≠ B)
    (h : Collinear ℝ ({A, B, x} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ t : ℝ, x = A + t • (B - A) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨p₀, v, hv⟩ := h
  have hA : A ∈ ({A, B, x} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
  have hB : B ∈ ({A, B, x} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
  have hx : x ∈ ({A, B, x} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
  obtain ⟨rA, hA'⟩ := hv A hA
  obtain ⟨rB, hB'⟩ := hv B hB
  obtain ⟨rx, hx'⟩ := hv x hx
  -- B - A = (rB - rA) • v
  have hBA : B - A = (rB - rA) • v := by rw [hA', hB']; ext i; simp [vadd_eq_add]; ring
  -- x - A = (rx - rA) • v
  have hxA : x - A = (rx - rA) • v := by rw [hA', hx']; ext i; simp [vadd_eq_add]; ring
  -- Since A ≠ B, we have rA ≠ rB
  have hr : rA ≠ rB := by
    intro hr_eq
    apply hAB
    rw [hA', hB', hr_eq]
  -- Let t = (rx - rA) / (rB - rA)
  use (rx - rA) / (rB - rA)
  -- Show x = A + t • (B - A)
  have hr' : rB - rA ≠ 0 := sub_ne_zero.mpr hr.symm
  rw [hBA]
  rw [hx', hA']
  rw [smul_smul]
  field_simp
  ext i
  simp [vadd_eq_add]
  ring

/-- A set of points with integral pairwise distances containing a non-degenerate triangle
is finite. -/
