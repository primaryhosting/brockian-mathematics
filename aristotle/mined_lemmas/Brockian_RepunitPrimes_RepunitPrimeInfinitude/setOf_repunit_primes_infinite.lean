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

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th base-ten repunit `R n = 1 + 10 + ⋯ + 10 ^ (n - 1)`, i.e. the natural number
whose decimal expansion consists of `n` ones. -/

theorem setOf_repunit_primes_infinite
    (h : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (repunit n)) :
    {q : ℕ | q.Prime ∧ ∃ n : ℕ, q = repunit n}.Infinite := by
  have h' : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsPrimeNat (repunit n) := by
    intro N
    obtain ⟨n, hn, hp⟩ := h N
    exact ⟨n, hn, isPrimeNat_iff_nat_prime.mpr hp⟩
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨q, hq, hqp, n, rfl⟩ := RepunitPrimeInfinitude h' a
  exact ⟨repunit n, ⟨isPrimeNat_iff_nat_prime.mp hqp, ⟨n, rfl⟩⟩, hq⟩

end RepunitPrimes
end Brockian

