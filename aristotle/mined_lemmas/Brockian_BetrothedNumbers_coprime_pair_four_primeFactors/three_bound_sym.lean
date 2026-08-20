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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma three_bound_sym {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
  have key : ∀ x y z : ℕ, x.Prime → y.Prime → z.Prime → x < y → y < z →
      x * y * z ≤ 4 * ((x - 1) * (y - 1) * (z - 1)) := by
    intro x y z hx hy hz hxy hyz
    exact three_bound hx.two_le (three_le_of_prime_lt hy hx.two_le hxy)
      (five_le_of_prime_lt hz (three_le_of_prime_lt hy hx.two_le hxy) hyz)
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · exact key a b c ha hb hc h1 h2
    · exact absurd h2 hbc
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · calc a * b * c = a * c * b := by ring
          _ ≤ 4 * ((a - 1) * (c - 1) * (b - 1)) := key a c b ha hc hb h3 h2
          _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring
      · exact absurd h3 hac
      · calc a * b * c = c * a * b := by ring
          _ ≤ 4 * ((c - 1) * (a - 1) * (b - 1)) := key c a b hc ha hb h3 h1
          _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring
  · exact absurd h1 hab
  · rcases lt_trichotomy a c with h2 | h2 | h2
    · calc a * b * c = b * a * c := by ring
        _ ≤ 4 * ((b - 1) * (a - 1) * (c - 1)) := key b a c hb ha hc h1 h2
        _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring
    · exact absurd h2 hac
    · rcases lt_trichotomy b c with h3 | h3 | h3
      · calc a * b * c = b * c * a := by ring
          _ ≤ 4 * ((b - 1) * (c - 1) * (a - 1)) := key b c a hb hc ha h3 h2
          _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring
      · exact absurd h3 hbc
      · calc a * b * c = c * b * a := by ring
          _ ≤ 4 * ((c - 1) * (b - 1) * (a - 1)) := key c b a hc hb ha h3 h1
          _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring

/-- For at most three distinct primes, `∏ p ≤ 4 * ∏ (p - 1)`. -/
