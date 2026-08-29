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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit: the base-ten number consisting of `n` digits `1`,
i.e. `repunit n = (10 ^ n - 1) / 9`. -/

theorem infinite_setOf_not_prime_repunit : {n : ℕ | ¬ Nat.Prime (repunit n)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨2 * (a + 2), ?_, by omega⟩
  intro hp
  have hprime := prime_of_prime_repunit hp
  have h2 : (2 : ℕ) ∣ 2 * (a + 2) := ⟨a + 2, rfl⟩
  rcases hprime.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

/-! ### Unconditional infinitude of prime divisors of repunits -/

/-- **Unconditional.** Every prime other than `2` and `5` divides some repunit. -/
