import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The argument is the classical Galois-theoretic one: the quintic `X ^ 5 - 4 * X + 2` is
irreducible over `ℚ` (Eisenstein at `2`), has exactly `3` real roots and hence exactly
`2` non-real complex roots, so its Galois group is the full symmetric group on its `5`
complex roots, which is not solvable.  Consequently none of its roots is expressible by
radicals, i.e. the general quintic equation admits no solution formula in radicals.
-/

open Function Polynomial Polynomial.Gal Ideal

namespace AbelRuffiniDeg5

attribute [local instance] splits_ℚ_ℂ

/-- The quintic `X ^ 5 - 4 * X + 2`, over an arbitrary commutative ring. -/

theorem exists_two_real_roots : ∃ x y : ℝ, x ≠ y ∧ aeval x (Q ℚ) = 0 ∧ aeval y (Q ℚ) = 0 := by
  set f : ℝ → ℝ := fun x : ℝ => aeval x (Q ℚ) with hfdef
  have hf : ∀ x : ℝ, f x = x ^ 5 - 4 * x + 2 := by intro x; simp [hfdef, Q]
  have hc : ∀ s : Set ℝ, ContinuousOn f s := fun s => (Q ℚ).continuousOn_aeval
  have h0 : f 0 = 2 := by rw [hf]; norm_num
  have h1 : f 1 = -1 := by rw [hf]; norm_num
  have h2 : f 2 = 26 := by rw [hf]; norm_num
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1) (hc _)
    (by rw [h0, h1]; norm_num : (0 : ℝ) ∈ Set.Ioo (f 1) (f 0))
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2) (hc _)
    (by rw [h1, h2]; norm_num : (0 : ℝ) ∈ Set.Ioo (f 1) (f 2))
  refine ⟨x, y, ?_, hx0, hy0⟩
  have hx1 := hx.2
  have hy1 := hy.1
  intro h
  subst h
  linarith

