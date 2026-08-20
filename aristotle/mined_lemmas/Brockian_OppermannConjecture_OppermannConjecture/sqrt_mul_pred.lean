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

/-
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture**: for every `n > 1` there is a prime strictly between
`n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`. -/

lemma sqrt_mul_pred (n : ℕ) (hn : 1 ≤ n) : Nat.sqrt (n * (n - 1)) = n - 1 := by
  have hlt : Nat.sqrt (n * (n - 1)) < n := by
    rw [Nat.sqrt_lt]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hge : n - 1 ≤ Nat.sqrt (n * (n - 1)) := by
    rw [Nat.le_sqrt]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- Oppermann's conjecture verified directly for `2 ≤ n ≤ 11`. -/
