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

namespace Brockian.RepunitPrimes

/-- The `n`-th base-ten repunit `Rₙ = 1 + 10 + ⋯ + 10ⁿ⁻¹ = (10ⁿ - 1)/9`. -/

theorem repunitPrimeInfinitude_iff :
    {n : ℕ | Nat.Prime (repunit n)}.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
        ∀ q : ℕ, q.Prime → q % (2 * p) = 1 → q * q ≤ repunit p → ¬ q ∣ repunit p := by
  refine ⟨fun hinf N => ?_, RepunitPrimeInfinitude⟩
  obtain ⟨p, hpmem, hpgt⟩ := hinf.exists_gt (max N 5)
  have hprime : Nat.Prime (repunit p) := hpmem
  have hp5 : 5 ≤ p := le_of_lt (lt_of_le_of_lt (le_max_right N 5) hpgt)
  refine ⟨p, lt_of_le_of_lt (le_max_left N 5) hpgt, prime_index_of_prime_repunit hprime,
    fun q hq _ hsq hdvd => ?_⟩
  have hqeq : q = repunit p := ((Nat.prime_dvd_prime_iff_eq hq hprime).mp hdvd)
  have h1 : 1 < repunit p := one_lt_repunit (by omega)
  subst hqeq
  nlinarith

end Brockian.RepunitPrimes

