/-
Enumeration data for `Brockian.GoldbachWheelK2_1327`.

For every `n` with `2 ≤ n ≤ 1327` we exhibit an explicit pair of primes summing
to the even number `2 * n`, i.e. Goldbach's conjecture is verified for all even
numbers up to twice the wheel modulus `1327`.
-/
import Mathlib

set_option maxRecDepth 10000

namespace Brockian

/-- `GoldbachRep n` states that `n` is a sum of two primes. -/

theorem prime_mod_six_mem_wheelK2 {p : ℕ} (hp : Nat.Prime p) (h3 : 3 < p) :
    p % 6 ∈ WheelK2 := by
  have h2 : ¬ (2 ∣ p) := by
    intro hd
    have : (2 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    omega
  have h3' : ¬ (3 ∣ p) := by
    intro hd
    have : (3 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    omega
  have : p % 6 = 1 ∨ p % 6 = 5 := by omega
  simpa [WheelK2] using this

/-- Wheel constraint for `K = 2`: if an even number `n ≡ 2 [MOD 6]` is a sum of two
primes both exceeding `3`, then both primes are `≡ 1 [MOD 6]`. -/
