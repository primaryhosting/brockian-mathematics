/-
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 2y² = 1` has a nontrivial integer solution,
i.e. a solution with `y ≠ 0`. -/

theorem pell_2_infinitely_many (N : ℤ) :
    ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ y > N := by
  -- iterate `(x, y) ↦ (3x + 4y, 2x + 3y)` starting from `(3, 2)`
  have key : ∀ n : ℕ, ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ 0 < x ∧ (n : ℤ) < y := by
    intro n
    induction n with
    | zero => exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩
    | succ n ih =>
      obtain ⟨x, y, hxy, hx, hy⟩ := ih
      have hn : (0:ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      have hx1 : (1:ℤ) ≤ x := hx
      have hy1 : (n:ℤ) + 1 ≤ y := hy
      refine ⟨3 * x + 4 * y, 2 * x + 3 * y, by linear_combination hxy, by linarith, ?_⟩
      push_cast
      linarith
  obtain ⟨x, y, hxy, _, hy⟩ := key (N.toNat + 1)
  refine ⟨x, y, hxy, lt_of_le_of_lt ?_ hy⟩
  have : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  push_cast
  linarith

end Math

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

