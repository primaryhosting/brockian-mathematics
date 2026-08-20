/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter

namespace Frontier

/-- `primeGap n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th prime
(so `p_0 = 2`, `p_1 = 3`, ...). -/

theorem boundedPrimeGaps_of_twin_prime_conjecture
    (H : ∀ M : ℕ, ∃ p, M ≤ p ∧ p.Prime ∧ (p + 2).Prime) : BoundedPrimeGaps := by
  rw [bounded_prime_gaps]
  refine ⟨2, fun N => ?_⟩
  obtain ⟨p, hpM, hp, hp2⟩ := H (max 3 (Nat.nth Nat.Prime N + 1))
  have hp3 : 3 ≤ p := le_trans (le_max_left _ _) hpM
  have hpN : Nat.nth Nat.Prime N < p := by
    have := le_trans (le_max_right 3 (Nat.nth Nat.Prime N + 1)) hpM
    omega
  refine ⟨Nat.count Nat.Prime p, ?_,
    le_of_eq (primeGap_count_eq_two_of_twin hp hp2 (by omega))⟩
  by_contra hlt
  push_neg at hlt
  have hcontra : Nat.nth Nat.Prime (Nat.count Nat.Prime p) < Nat.nth Nat.Prime N :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr hlt
  rw [Nat.nth_count hp] at hcontra
  omega

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

