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
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- Geometric sum identity in `ℕ`, phrased so as to avoid truncated subtraction. -/

lemma four_mul_le_fifteen_mul_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) :
    4 * (p * q * r) ≤ 15 * ((p - 1) * ((q - 1) * (r - 1))) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq3 : 3 ≤ q := by omega
  have hr5 : 5 ≤ r := by
    have h4 : r ≠ 4 := by rintro rfl; norm_num at hr
    omega
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith [hp2, hq3, hr5, Nat.zero_le (p' * q'), Nat.zero_le (q' * r'), Nat.zero_le (p' * r'),
    Nat.zero_le (p' * q' * r')]

/-- For a set of at most three primes, `4 ∏ p ≤ 15 ∏ (p-1)`. -/
