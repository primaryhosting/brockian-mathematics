/-
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- The Pell equation `x² - 2·y² = 1` has a nontrivial integer solution, i.e. one
with `y ≠ 0` (equivalently, other than `(±1, 0)`). -/
theorem pell_2 : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 := by
  refine ⟨3, 2, by norm_num, by norm_num⟩

/-- The Brahmagupta composition step: from a solution `(x, y)` of `x² - 2y² = 1`
we obtain a new solution `(3x + 4y, 2x + 3y)`. -/
theorem pell_2_step {x y : ℤ} (h : x ^ 2 - 2 * y ^ 2 = 1) :
    (3 * x + 4 * y) ^ 2 - 2 * (2 * x + 3 * y) ^ 2 = 1 := by
  linear_combination h

/-- Iterating the composition step gives solutions with arbitrarily large `y`,
so the Pell equation `x² - 2y² = 1` has infinitely many integer solutions. -/
theorem pell_2_infinite (N : ℤ) : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ N < y := by
  -- It suffices to produce, for each `n : ℕ`, a solution with `y ≥ n`.
  have key : ∀ n : ℕ, ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ 1 ≤ x ∧ (n : ℤ) < y := by
    intro n
    induction n with
    | zero => exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩
    | succ n ih =>
      obtain ⟨x, y, hxy, hx, hy⟩ := ih
      refine ⟨3 * x + 4 * y, 2 * x + 3 * y, pell_2_step hxy, by linarith, by
        have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
        push_cast
        linarith⟩
  obtain ⟨x, y, hxy, _, hy⟩ := key (N.toNat)
  exact ⟨x, y, hxy, lt_of_le_of_lt (Int.self_le_toNat N) hy⟩

/-- The solution set of the Pell equation `x² - 2y² = 1` in `ℤ × ℤ` is infinite. -/
theorem pell_2_solution_set_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 2 * p.2 ^ 2 = 1}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := (hfin.image Prod.snd).bddAbove
  obtain ⟨x, y, hxy, hy⟩ := pell_2_infinite N
  exact absurd (hN ⟨(x, y), hxy, rfl⟩) (not_le.mpr hy)

end Math

