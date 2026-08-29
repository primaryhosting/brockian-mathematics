import Mathlib
/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 3y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (witness: `x = 2`, `y = 1`). -/
theorem pell_3 : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨2, 1, by norm_num, by norm_num⟩

/-- Composition step: from a solution `(x, y)` we get another one,
`(2x + 3y, x + 2y)`. -/
theorem pell_3_step {x y : ℤ} (h : x ^ 2 - 3 * y ^ 2 = 1) :
    (2 * x + 3 * y) ^ 2 - 3 * (x + 2 * y) ^ 2 = 1 := by nlinarith [h]

/-- There are arbitrarily large solutions of `x² - 3y² = 1`; in particular
there are infinitely many integer solutions. -/
theorem pell_3_unbounded (N : ℤ) : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N < (n : ℤ) := ⟨(N + 1).toNat, by omega⟩
  suffices h : ∀ m : ℕ, ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ (m : ℤ) < y by
    obtain ⟨x, y, hxy, hy⟩ := h n
    exact ⟨x, y, hxy, lt_trans hn hy⟩
  intro m
  induction m with
  | zero => exact ⟨2, 1, by norm_num, by norm_num⟩
  | succ k ih =>
      obtain ⟨x, y, hxy, hy⟩ := ih
      have hx : 1 ≤ x ∨ x ≤ -1 := by
        rcases lt_trichotomy x 0 with h | h | h
        · right; omega
        · exfalso; subst h; nlinarith
        · left; omega
      rcases hx with hx | hx
      · exact ⟨2 * x + 3 * y, x + 2 * y, pell_3_step hxy, by push_cast; omega⟩
      · refine ⟨2 * (-x) + 3 * y, -x + 2 * y, pell_3_step (by nlinarith), ?_⟩
        push_cast; omega

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

