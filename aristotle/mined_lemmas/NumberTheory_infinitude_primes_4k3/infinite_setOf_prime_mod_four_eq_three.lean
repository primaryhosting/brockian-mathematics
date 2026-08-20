/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-! ### An elementary Euclid-style argument

Every natural number congruent to `3` mod `4` has a prime factor congruent to `3` mod `4`,
because a product of numbers congruent to `1` mod `4` is again congruent to `1` mod `4`.
Applying this to `4 * N ! - 1` produces a prime `> N` congruent to `3` mod `4`. -/

/-- If `q ≡ 1 [MOD 4]` and `q * m ≡ 3 [MOD 4]`, then `m ≡ 3 [MOD 4]`. -/

theorem infinite_setOf_prime_mod_four_eq_three :
    {p : ℕ | Nat.Prime p ∧ p % 4 = 3}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, hpN, hp, hpmod⟩ := infinitude_primes_4k3 N
  have : p ≤ N := hN ⟨hp, hpmod⟩
  omega

end NumberTheory

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

