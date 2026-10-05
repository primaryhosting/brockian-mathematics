/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime divisors. -/

lemma three_mul_rad_le {m : ℕ} (hm : m ≠ 0) (h9 : 9 ∣ m) : 3 * rad m ≤ m := by
  obtain ⟨t, rfl⟩ := h9
  have ht : t ≠ 0 := by rintro rfl; simp at hm
  have h1 : (9 : ℕ) * t = 3 * (3 * t) := by ring
  rw [h1, rad_three_mul (by positivity) ⟨t, rfl⟩]
  have h2 : rad (3 * t) ≤ 3 * t :=
    Nat.le_of_dvd (by positivity) (rad_dvd (3 * t))
  omega

