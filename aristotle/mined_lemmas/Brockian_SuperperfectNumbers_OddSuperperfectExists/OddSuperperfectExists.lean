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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

theorem OddSuperperfectExists :
    (∃ n, Odd n ∧ Superperfect n) ↔
      ∃ n, 1000 < n ∧ Odd n ∧ Superperfect n ∧ σ 1 n < 2 * n ∧
        (∀ a : ℕ, σ 1 n ≠ 2 ^ a) ∧ (3 ∣ n → IsSquare n) := by
  constructor
  · rintro ⟨n, hodd, hsp⟩
    have hn1000 : 1000 < n := by
      by_contra hle
      exact no_odd_superperfect_le_1000 n (by omega) hodd hsp
    exact ⟨n, hn1000, hodd, hsp, sigma_lt_two_mul_of_superperfect (by omega) hsp,
      sigma_ne_two_pow_of_superperfect hsp,
      fun h3 => isSquare_of_three_dvd hodd hsp h3⟩
  · rintro ⟨n, -, hodd, hsp, -⟩
    exact ⟨n, hodd, hsp⟩

end Brockian.SuperperfectNumbers

