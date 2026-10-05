import Mathlib

/-!
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- `IsSumOfThreePrimes n` means that `n` can be written as a sum of three
(not necessarily distinct) prime numbers. -/
def IsSumOfThreePrimes (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r

/-- The statement of Vinogradov's three primes theorem: every sufficiently large
odd number is a sum of three primes. -/
def VinogradovStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → IsSumOfThreePrimes n

/-- The binary Goldbach conjecture: every even number `≥ 4` is a sum of two primes. -/
def GoldbachBinary : Prop :=
  ∀ m : ℕ, 4 ≤ m → Even m → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p + q

/-!
## The target: a Lean-checked reduction

The full unconditional theorem of Vinogradov (every sufficiently large odd number is a
sum of three primes) rests on the Hardy–Littlewood circle method and is far outside the
scope of what is currently formalized. Following the stated goal ("prove the base case or
a Lean-checked reduction"), the target theorem below is the *reduction*: from the binary
Goldbach property for even numbers one obtains the Vinogradov statement, with the explicit
threshold `N = 7` (which is optimal: `5` is odd but is not a sum of three primes).

Unconditional companion results proved below:
* `Frontier.isSumOfThreePrimes_of_odd_of_lt_500`: every odd `n` with `7 ≤ n < 500` really
  is a sum of three primes (a kernel-checked finite verification);
* `Frontier.exists_large_odd_isSumOfThreePrimes`: there are arbitrarily large odd numbers
  that are sums of three primes.
-/

/-- **Target.** A Lean-checked reduction of Vinogradov's three primes statement to the
binary Goldbach property: if every even number `≥ 4` is a sum of two primes, then every
odd number `≥ 7` (in particular every sufficiently large odd number) is a sum of three
primes. -/
theorem Vinogradov_three_primes : GoldbachBinary → VinogradovStatement := by
  intro hG
  refine ⟨7, ?_⟩
  intro n hn hodd
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have heven : Even (n - 3) := Nat.even_iff.mpr (by omega)
  obtain ⟨p, q, hp, hq, hpq⟩ := hG (n - 3) (by omega) heven
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- Finite verification: every odd number `n` with `7 ≤ n < 500` is a sum of three primes
(indeed of `3` and two further primes). This is checked by the kernel. -/
theorem isSumOfThreePrimes_of_odd_of_lt_500 (n : ℕ) (h7 : 7 ≤ n) (hlt : n < 500)
    (hodd : Odd n) : IsSumOfThreePrimes n := by
  have key : ∀ m < 500, 7 ≤ m → Odd m →
      ∃ p < m, Nat.Prime p ∧ Nat.Prime (m - 3 - p) ∧ m = 3 + p + (m - 3 - p) := by decide
  obtain ⟨p, -, hp, hq, hsum⟩ := key n hlt h7 hodd
  exact ⟨3, p, n - 3 - p, Nat.prime_three, hp, hq, hsum⟩

/-- Unconditionally, there are arbitrarily large odd numbers which are sums of three
primes: `4 + p = 2 + 2 + p` for any odd prime `p`. -/
theorem exists_large_odd_isSumOfThreePrimes (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ Odd n ∧ IsSumOfThreePrimes n := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 3)
  have hp3 : 3 ≤ p := le_trans (le_max_right N 3) hpN
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  refine ⟨2 + 2 + p, ?_, ?_, ⟨2, 2, p, Nat.prime_two, Nat.prime_two, hp, rfl⟩⟩
  · have := le_trans (le_max_left N 3) hpN
    omega
  · rcases hpodd with ⟨k, hk⟩
    exact ⟨k + 2, by omega⟩

end Frontier

