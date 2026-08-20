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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma three_primes_bound {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a * b * c ≤ 4 * ((a - 1) * ((b - 1) * (c - 1))) := by
  have main : ∀ x y z : ℕ, x.Prime → y.Prime → z.Prime → x < y → y < z →
      x * y * z ≤ 4 * ((x - 1) * ((y - 1) * (z - 1))) := by
    intro x y z hx hy hz hxy hyz
    exact three_primes_bound_sorted hx hy hz hxy hyz
  rcases Nat.lt_or_ge a b with h1 | h1
  · rcases Nat.lt_or_ge b c with h2 | h2
    · have := main a b c ha hb hc h1 h2; linarith [this]
    · have h2' : c < b := by omega
      rcases Nat.lt_or_ge a c with h3 | h3
      · have := main a c b ha hc hb h3 h2'
        calc a * b * c = a * c * b := by ring
          _ ≤ 4 * ((a-1) * ((c-1) * (b-1))) := this
          _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring
      · have h3' : c < a := by omega
        have := main c a b hc ha hb h3' h1
        calc a * b * c = c * a * b := by ring
          _ ≤ 4 * ((c-1) * ((a-1) * (b-1))) := this
          _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring
  · have h1' : b < a := by omega
    rcases Nat.lt_or_ge a c with h2 | h2
    · have := main b a c hb ha hc h1' h2
      calc a * b * c = b * a * c := by ring
        _ ≤ 4 * ((b-1) * ((a-1) * (c-1))) := this
        _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring
    · have h2' : c < a := by omega
      rcases Nat.lt_or_ge b c with h3 | h3
      · have := main b c a hb hc ha h3 h2'
        calc a * b * c = b * c * a := by ring
          _ ≤ 4 * ((b-1) * ((c-1) * (a-1))) := this
          _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring
      · have h3' : c < b := by omega
        have := main c b a hc hb ha h3' h1'
        calc a * b * c = c * b * a := by ring
          _ ≤ 4 * ((c-1) * ((b-1) * (a-1))) := this
          _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring

/-- If a finite set of primes has at most three elements then
`∏ p ≤ 4 * ∏ (p - 1)`. -/
