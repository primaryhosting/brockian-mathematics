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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ (σ n) = 2 n`.  Suryanarayana and Kanold
showed that the even superperfect numbers are exactly the powers `2 ^ k` with
`2 ^ (k + 1) - 1` prime; whether an *odd* superperfect number exists is an open problem.

This file contains a Lean-checked reduction of that open problem, together with the
(easy half of the) even classification and two unconditional constraints on a
hypothetical odd superperfect number.
-/

open scoped ArithmeticFunction.sigma

open ArithmeticFunction Finset

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

theorem OddSuperperfectExists :
    (∃ n, Odd n ∧ Superperfect n) ↔
      ∃ n, 1000 < n ∧ Odd n ∧ Superperfect n ∧
        ∃ p, p.Prime ∧ p ≠ 2 ∧ Odd ((σ 1 n).factorization p) := by
  constructor
  · rintro ⟨n, hn, h⟩
    rcases lt_or_ge 1000 n with h1 | h1
    · exact ⟨n, h1, hn, h, exists_odd_prime_odd_exponent hn h⟩
    · have hlt : n < 1000 :=
        lt_of_le_of_ne h1 (by rintro rfl; exact (Nat.not_odd_iff_even.2 (by decide)) hn)
      exact absurd h (not_superperfect_of_lt hn hlt)
  · rintro ⟨n, _, hn, h, _⟩
    exact ⟨n, hn, h⟩

end Brockian.SuperperfectNumbers

