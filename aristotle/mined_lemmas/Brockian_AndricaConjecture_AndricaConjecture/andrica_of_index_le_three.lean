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

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AndricaConjecture

/-- **Oppermann's conjecture** (open): for every `n ≥ 2` there is a prime strictly between
`n²` and `n² + n`, and a prime strictly between `n² + n` and `(n+1)²`. -/

theorem andrica_of_index_le_three {n : ℕ} (hn : n ≤ 3) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1)) - Real.sqrt (Nat.nth Nat.Prime n) < 1 := by
  interval_cases n
  · rw [show Nat.nth Nat.Prime 0 = 2 by norm_num, show Nat.nth Nat.Prime 1 = 3 by norm_num]
    exact sqrt_sub_sqrt_lt_one (m := 1) (by norm_num) (by norm_num)
  · rw [show Nat.nth Nat.Prime 1 = 3 by norm_num, show Nat.nth Nat.Prime 2 = 5 by norm_num]
    exact sqrt_sub_sqrt_lt_one (m := 1) (by norm_num) (by norm_num)
  · rw [show Nat.nth Nat.Prime 2 = 5 by norm_num, show Nat.nth Nat.Prime 3 = 7 by norm_num]
    exact sqrt_sub_sqrt_lt_one (m := 2) (by norm_num) (by norm_num)
  · rw [show Nat.nth Nat.Prime 3 = 7 by norm_num, show Nat.nth Nat.Prime 4 = 11 by norm_num]
    exact sqrt_sub_sqrt_lt_one (m := 2) (by norm_num) (by norm_num)

/-- **Andrica's conjecture**, conditional on Oppermann's conjecture:
for consecutive primes `pₙ < pₙ₊₁` one has `√pₙ₊₁ - √pₙ < 1`. -/
