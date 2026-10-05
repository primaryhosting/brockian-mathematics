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

lemma four_mul_prod_three_le' {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    4 * (a * b * c) ≤ 15 * ((a - 1) * (b - 1) * (c - 1)) := by
  rcases Nat.lt_or_ge a b with h1 | h1
  · rcases Nat.lt_or_ge b c with h2 | h2
    · exact four_mul_prod_three_le ha hc h1 h2
    · have h2 : c < b := lt_of_le_of_ne h2 (Ne.symm hbc)
      rcases Nat.lt_or_ge a c with h3 | h3
      · have hacb := four_mul_prod_three_le ha hb h3 h2
        calc 4 * (a * b * c) = 4 * (a * c * b) := by ring
          _ ≤ 15 * ((a - 1) * (c - 1) * (b - 1)) := hacb
          _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring
      · have h3 : c < a := lt_of_le_of_ne h3 (Ne.symm hac)
        have hcab := four_mul_prod_three_le hc hb h3 h1
        calc 4 * (a * b * c) = 4 * (c * a * b) := by ring
          _ ≤ 15 * ((c - 1) * (a - 1) * (b - 1)) := hcab
          _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring
  · have h1 : b < a := lt_of_le_of_ne h1 (Ne.symm hab)
    rcases Nat.lt_or_ge a c with h2 | h2
    · have hbac := four_mul_prod_three_le hb hc h1 h2
      calc 4 * (a * b * c) = 4 * (b * a * c) := by ring
        _ ≤ 15 * ((b - 1) * (a - 1) * (c - 1)) := hbac
        _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring
    · have h2 : c < a := lt_of_le_of_ne h2 (Ne.symm hac)
      rcases Nat.lt_or_ge b c with h3 | h3
      · have hbca := four_mul_prod_three_le hb ha h3 h2
        calc 4 * (a * b * c) = 4 * (b * c * a) := by ring
          _ ≤ 15 * ((b - 1) * (c - 1) * (a - 1)) := hbca
          _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring
      · have h3 : c < b := lt_of_le_of_ne h3 (Ne.symm hbc)
        have hcba := four_mul_prod_three_le hc ha h3 h1
        calc 4 * (a * b * c) = 4 * (c * b * a) := by ring
          _ ≤ 15 * ((c - 1) * (b - 1) * (a - 1)) := hcba
          _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring

/-- For a set of at most three primes, `4 ∏ p ≤ 15 ∏ (p - 1)`; equivalently
`∏ p / (p - 1) ≤ 15 / 4 < 4`. -/
