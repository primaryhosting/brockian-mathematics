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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Nat

/-- Existence of a "fortunate offset": for every `n` there is some `m > 1` such that
`n# + m` is prime, where `n#` is the primorial of `n`.  This follows from Bertrand's
postulate applied to `n# + 1`. -/

theorem exists_fortunate (n : ℕ) : ∃ m, 1 < m ∧ Nat.Prime (primorial n + m) := by
  obtain ⟨p, hp, hlt, -⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (primorial n + 1) (by positivity)
  refine ⟨p - primorial n, by omega, ?_⟩
  have : primorial n + (p - primorial n) = p := by omega
  rw [this]; exact hp

/-- The Fortunate number of `n`: the least `m > 1` such that `n# + m` is prime,
where `n#` denotes the primorial of `n` (the product of all primes `≤ n`). -/
