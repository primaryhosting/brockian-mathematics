/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and
the sum of the divisors of each equals `m + n + 1`. -/

lemma four_mul_prod_three_le {a b c : ℕ} (ha : a.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) :
    4 * (a * b * c) ≤ 15 * ((a - 1) * (b - 1) * (c - 1)) := by
  have ha2 : 2 ≤ a := ha.two_le
  have hb3 : 3 ≤ b := by omega
  have hc5 : 5 ≤ c := by
    have h4 : c ≠ 4 := by rintro rfl; norm_num at hc
    omega
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 2 := ⟨a - 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = y + 3 := ⟨b - 3, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ z, c = z + 5 := ⟨c - 5, by omega⟩
  have e1 : x + 2 - 1 = x + 1 := by omega
  have e2 : y + 3 - 1 = y + 2 := by omega
  have e3 : z + 5 - 1 = z + 4 := by omega
  rw [e1, e2, e3]
  nlinarith [Nat.zero_le x, Nat.zero_le y, Nat.zero_le z, Nat.zero_le (x * y),
    Nat.zero_le (y * z), Nat.zero_le (x * z), Nat.zero_le (x * y * z)]

/-- Symmetric version of `four_mul_prod_three_le`. -/
