import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

lemma cos_eq_one_of_fixed {t : ℝ} {y : E} (hy : RY t • y = y) (hax : y 0 ≠ 0 ∨ y 2 ≠ 0) :
    Real.cos t = 1 := by
  obtain ⟨h0, h2⟩ := RY_smul_apply t y
  have e0 : Real.cos t * y 0 + Real.sin t * y 2 = y 0 := by
    rw [← h0, hy]
  have e2 : -(Real.sin t) * y 0 + Real.cos t * y 2 = y 2 := by
    rw [← h2, hy]
  have hpyth := Real.sin_sq_add_cos_sq t
  by_contra hcos
  have hA : (Real.cos t - 1) * y 0 + Real.sin t * y 2 = 0 := by linarith
  have hB : -(Real.sin t) * y 0 + (Real.cos t - 1) * y 2 = 0 := by linarith
  have hne : (2 - 2 * Real.cos t) ≠ 0 := fun hc => hcos (by linarith)
  have h1 : (2 - 2 * Real.cos t) * y 0 = 0 := by
    linear_combination (Real.cos t - 1) * hA - Real.sin t * hB - y 0 * hpyth
  have h2' : (2 - 2 * Real.cos t) * y 2 = 0 := by
    linear_combination Real.sin t * hA + (Real.cos t - 1) * hB - y 2 * hpyth
  rcases hax with h | h
  · exact h ((mul_eq_zero.mp h1).resolve_left hne)
  · exact h ((mul_eq_zero.mp h2').resolve_left hne)

/-- There is a rotation about the `y`-axis moving a given countable set, disjoint from the
`y`-axis, completely off itself, together with all of its positive powers. -/
