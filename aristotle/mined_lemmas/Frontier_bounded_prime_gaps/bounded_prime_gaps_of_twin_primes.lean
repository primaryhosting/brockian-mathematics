import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- `nthPrime n` is the `n`-th prime number, counting from `nthPrime 0 = 2`. -/

theorem bounded_prime_gaps_of_twin_primes
    (h : ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ (p + 2).Prime) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  refine bounded_prime_gaps_of_bounded_pairs 2 fun N => ?_
  obtain ⟨p, hN, hp, hp2⟩ := h N
  exact ⟨p, p + 2, hN, hp, hp2, by omega, le_rfl⟩

end Frontier

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

