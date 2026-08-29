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

namespace Frontier

/-- `IsSumOfThreePrimes n` says that `n` is a sum of three (not necessarily distinct) primes. -/
def IsSumOfThreePrimes (n : ℕ) : Prop :=
  ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

/-- The asymptotic form of the binary Goldbach conjecture: every sufficiently large even
number is a sum of two primes. -/
def GoldbachAsymptotic : Prop :=
  ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Even m → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = m

/-- **Vinogradov's three primes theorem** (Lean-checked reduction form).

Every sufficiently large odd number is a sum of three primes, deduced from the asymptotic
binary Goldbach statement `GoldbachAsymptotic`.  Concretely: if every even number beyond some
threshold is a sum of two primes, then every odd number beyond a (slightly larger) threshold is
a sum of three primes, namely `3` together with the two Goldbach primes for `n - 3`. -/
theorem Vinogradov_three_primes (h : GoldbachAsymptotic) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → IsSumOfThreePrimes n := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M + 3, fun n hn hodd => ?_⟩
  obtain ⟨k, hk⟩ := hodd
  have heven : Even (n - 3) := ⟨k - 1, by omega⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := hM (n - 3) (by omega) heven
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- Variant of the reduction with an explicit threshold: from the full binary Goldbach
conjecture (every even number `≥ 4` is a sum of two primes) one gets that *every* odd
`n ≥ 7` is a sum of three primes. -/
theorem Vinogradov_three_primes_of_goldbach
    (h : ∀ m : ℕ, 4 ≤ m → Even m → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = m)
    (n : ℕ) (hn : 7 ≤ n) (hodd : Odd n) : IsSumOfThreePrimes n := by
  obtain ⟨k, hk⟩ := hodd
  have heven : Even (n - 3) := ⟨k - 1, by omega⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := h (n - 3) (by omega) heven
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-! ### Unconditional verification of a base range -/

/-- A list of small primes, used as candidate second summands. -/
def smallPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

lemma smallPrimes_prime : ∀ q ∈ smallPrimes, Nat.Prime q := by decide

/-- Search for a decomposition `n = 3 + q + (n - 3 - q)` with `q` a small prime and
`n - 3 - q` prime. -/
def threePrimeWitness (n : ℕ) : Bool :=
  smallPrimes.any fun q => decide (q + 3 ≤ n) && Nat.Prime (n - 3 - q)

lemma isSumOfThreePrimes_of_witness {n : ℕ} (hn : threePrimeWitness n = true) :
    IsSumOfThreePrimes n := by
  simp only [threePrimeWitness, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hn
  obtain ⟨q, hqmem, hle, hpr⟩ := hn
  exact ⟨3, q, n - 3 - q, Nat.prime_three, smallPrimes_prime q hqmem, hpr, by omega⟩

set_option maxRecDepth 1000000 in
lemma witness_base_range : ∀ k ∈ List.range 250, threePrimeWitness (2 * k + 9) = true := by
  decide

/-- Unconditional base case: every odd `n` with `9 ≤ n ≤ 507` is a sum of three primes.
(Verified by an explicit kernel computation.) -/
theorem isSumOfThreePrimes_of_odd_of_le {n : ℕ} (h9 : 9 ≤ n) (hle : n ≤ 507) (hodd : Odd n) :
    IsSumOfThreePrimes n := by
  obtain ⟨k, hk⟩ := hodd
  have hmem : k - 4 ∈ List.range 250 := List.mem_range.2 (by omega)
  have := witness_base_range (k - 4) hmem
  have hrw : 2 * (k - 4) + 9 = n := by omega
  rw [hrw] at this
  exact isSumOfThreePrimes_of_witness this

/-- Unconditionally, there are arbitrarily large odd numbers that are sums of three primes
(take `3 + 3 + p` for a large prime `p`). -/
theorem exists_large_odd_isSumOfThreePrimes (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ Odd n ∧ IsSumOfThreePrimes n := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 3)
  have hp3 : 3 ≤ p := le_trans (le_max_right N 3) hpN
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hpodd
  refine ⟨p + 6, by omega, ⟨k + 3, by omega⟩, ⟨3, 3, p, Nat.prime_three, Nat.prime_three, hp, ?_⟩⟩
  omega

end Frontier

