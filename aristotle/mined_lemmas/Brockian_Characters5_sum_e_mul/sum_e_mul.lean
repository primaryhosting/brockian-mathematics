-- # Sum E Mul
-- Category: Characters
-- Target: Brockian.Characters5.sum_e_mul
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)

import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  have hs : omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
    have h := sum_omega_pow
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one] at h
    exact h
  have h1 : (1 : ZMod 5) ≠ 0 := by decide
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have h3 : (3 : ZMod 5) ≠ 0 := by decide
  have h4 : (4 : ZMod 5) ≠ 0 := by decide
  rcases zmod_five_cases a with rfl | rfl | rfl | rfl | rfl <;>
    simp only [sum_univ_zmod_five, e] <;>
    norm_num [ZMod.val, h1, h2, h3, h4] <;>
    linear_combination hs

end Brockian.Characters5

