import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian

/-- Trial division helper: `noFactorFrom f d n` is `true` when none of
`d, d+1, …` (up to `f` steps, stopping as soon as the divisor squared exceeds `n`)
divides `n`. -/

theorem coprime_six_of_mod {p : ℕ} (h : p % 6 = 1 ∨ p % 6 = 5) : Nat.Coprime p 6 := by
  have : Nat.gcd 6 p = Nat.gcd (p % 6) 6 := Nat.gcd_rec 6 p
  rcases h with h | h <;>
    · rw [h] at this
      simp [Nat.Coprime, Nat.gcd_comm p 6, this]

/-- The verified wheel table: for every `m` with `5 ≤ m ≤ 525` the even number `2 * m`
splits as `p + (2 * m - p)` with both summands prime and coprime to the wheel modulus `6`,
where `p` is drawn from the fixed list of wheel primes below. -/
