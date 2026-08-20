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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
A natural number `n` is *quasiperfect* if `σ n = 2 * n + 1`, i.e. the sum of the proper
divisors of `n` (including `1`) equals `n + 1`.  No quasiperfect number is known, and their
existence is an open problem.

This file proves the classical structural constraints (Cattaneo, 1951): a quasiperfect number
must be an odd perfect square, and it cannot be a prime power.  The main theorem
`QuasiperfectExists` is the resulting *reduction*: a quasiperfect number exists if and only if
there is an odd `k > 1`, not a prime power, whose square is quasiperfect.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of all of its
divisors equals `2 * n + 1`. -/

theorem QuasiperfectExists :
    (∃ n : ℕ, Quasiperfect n) ↔
      ∃ k : ℕ, Odd k ∧ 1 < k ∧ (¬ ∃ p e : ℕ, p.Prime ∧ k = p ^ e) ∧ Quasiperfect (k ^ 2) := by
  constructor
  · rintro ⟨n, hq⟩
    obtain ⟨k, hk⟩ := hq.isSquare
    have hodd := hq.odd
    have hn1 : n ≠ 1 := by rintro rfl; exact not_quasiperfect_one hq
    have hk2 : n = k ^ 2 := by rw [hk]; ring
    have hqk : Quasiperfect (k ^ 2) := hk2 ▸ hq
    refine ⟨k, (Nat.odd_mul.mp (hk ▸ hodd)).1, ?_, ?_, hqk⟩
    · rcases Nat.lt_or_ge k 2 with hlt | hge
      · interval_cases k <;> simp_all
      · omega
    · rintro ⟨p, e, hp, rfl⟩
      exact not_quasiperfect_prime_pow (p := p) (e := e * 2) hp (by simpa [pow_mul] using hqk)
  · rintro ⟨k, -, -, -, hq⟩
    exact ⟨k ^ 2, hq⟩

end Brockian.QuasiperfectNumbers

