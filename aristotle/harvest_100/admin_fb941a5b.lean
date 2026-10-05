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
def Superperfect (n : ℕ) : Prop := σ 1 (σ 1 n) = 2 * n

instance decidableSuperperfect (n : ℕ) : Decidable (Superperfect n) :=
  inferInstanceAs (Decidable (σ 1 (σ 1 n) = 2 * n))

/-! ### Basic divisor-sum estimates -/

/-- If `a` is a divisor of `N` with `1 < a < N`, then `1`, `a` and `N` are three distinct
divisors of `N`, so `σ N ≥ N + a + 1`. -/
theorem add_add_one_le_sigma_of_dvd {N a : ℕ} (ha : a ∣ N) (h1 : 1 < a) (h2 : a < N) :
    N + a + 1 ≤ σ 1 N := by
  have hN : N ≠ 0 := by omega
  have hsub : ({1, a, N} : Finset ℕ) ⊆ N.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.one_mem_divisors.mpr hN
    · exact Nat.mem_divisors.mpr ⟨ha, hN⟩
    · exact Nat.mem_divisors_self _ hN
  have key := Finset.sum_le_sum_of_subset (f := fun d => d) hsub
  dsimp only at key
  rw [ArithmeticFunction.sigma_one_apply]
  have hs : ∑ d ∈ ({1, a, N} : Finset ℕ), d = 1 + a + N := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_singleton]
    ring
  omega

/-- For `N > 1` we have `σ N ≥ N + 1`. -/
theorem succ_le_sigma {N : ℕ} (hN : 1 < N) : N + 1 ≤ σ 1 N := by
  have hN0 : N ≠ 0 := by omega
  have hsub : ({1, N} : Finset ℕ) ⊆ N.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.one_mem_divisors.mpr hN0
    · exact Nat.mem_divisors_self _ hN0
  have key := Finset.sum_le_sum_of_subset (f := fun d => d) hsub
  dsimp only at key
  rw [ArithmeticFunction.sigma_one_apply]
  have hs : ∑ d ∈ ({1, N} : Finset ℕ), d = 1 + N := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  omega

/-- The sum of divisors of a power of two: `σ (2 ^ k) = 2 ^ (k + 1) - 1`. -/
theorem sigma_two_pow (k : ℕ) : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      ring_nf
      omega

/-- The sum of divisors of a prime: `σ p = p + 1`. -/
theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simp [Finset.sum_range_succ] at h
  simpa [add_comm] using h

/-! ### Even superperfect numbers -/

/-- If `2 ^ (k + 1) - 1` is prime, then `2 ^ k` is superperfect.  (So superperfect numbers
do exist; the open question is whether an odd one does.) -/
theorem superperfect_two_pow_of_prime {k : ℕ} (hp : Nat.Prime (2 ^ (k + 1) - 1)) :
    Superperfect (2 ^ k) := by
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  unfold Superperfect
  rw [sigma_two_pow, sigma_prime hp]
  have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  omega

example : Superperfect 16 := by decide

/-! ### Constraints on odd superperfect numbers -/

/-- `1` is not superperfect. -/
theorem not_superperfect_one : ¬ Superperfect 1 := by decide

/-- A superperfect number `n > 1` is deficient: `σ n < 2 * n`. -/
theorem sigma_lt_two_mul_of_superperfect {n : ℕ} (hn : 1 < n) (h : Superperfect n) :
    σ 1 n < 2 * n := by
  have h1 : n + 1 ≤ σ 1 n := succ_le_sigma hn
  have h2 : σ 1 n + 1 ≤ σ 1 (σ 1 n) := succ_le_sigma (by omega)
  rw [h] at h2
  omega

/-- The sum of divisors of a superperfect number is never a power of two. -/
theorem sigma_ne_two_pow_of_superperfect {n : ℕ} (h : Superperfect n) (a : ℕ) :
    σ 1 n ≠ 2 ^ a := by
  intro ha
  have h2 : σ 1 (σ 1 n) = 2 * n := h
  rw [ha, sigma_two_pow] at h2
  have h3 : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
  have h4 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  omega

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- There is no odd superperfect number up to `1000` (exhaustive verification). -/
theorem no_odd_superperfect_le_1000 : ∀ n ≤ 1000, Odd n → ¬ Superperfect n := by
  have key : ∀ n ∈ Finset.range 1001, n % 2 = 1 → σ 1 (σ 1 n) ≠ 2 * n := by decide +kernel
  intro n hn ho hsp
  exact key n (Finset.mem_range.mpr (by omega)) (Nat.odd_iff.mp ho) hsp

/-! ### Parity of the sum of divisors -/

/-- The prime factorisation of a nonzero natural number. -/
theorem prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-- If all exponents in the prime factorization of `n ≠ 0` are even, then `n` is a square. -/
theorem isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  refine (prod_primeFactors_pow_factorization hn).symm.trans
    (Finset.prod_congr rfl fun p _ => ?_)
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := h p
  omega

/-- If `n` is odd with an odd sum of divisors, then every exponent in its prime factorization
is even. -/
theorem factorization_even_of_odd_sigma {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) (h : Odd (σ 1 n))
    (p : ℕ) : Even (n.factorization p) := by
  by_contra hodde
  rw [Nat.not_even_iff_odd] at hodde
  have hp : p ∈ n.primeFactors := by
    by_contra hpm
    have h0 : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (by
      simpa [Nat.support_factorization] using hpm)
    rw [h0] at hodde
    simp at hodde
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpodd : Odd p := by
    rcases hpp.eq_two_or_odd' with rfl | h2
    · exact absurd (Nat.dvd_of_mem_primeFactors hp) (by
        rintro h2
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2))
    · exact h2
  have hev : Even (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) := by
    rw [Finset.even_sum_iff_even_card_odd]
    have hfil : {x ∈ Finset.range (n.factorization p + 1) | Odd (p ^ x)}
        = Finset.range (n.factorization p + 1) :=
      Finset.filter_true_of_mem fun x _ => hpodd.pow
    rw [hfil, Finset.card_range]
    exact hodde.add_one
  have hdvd : (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) ∣ σ 1 n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hn]
    exact Finset.dvd_prod_of_mem _ hp
  exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hev).trans hdvd))) h

/-- An odd number with an odd sum of divisors is a perfect square. -/
theorem isSquare_of_odd_of_odd_sigma {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) (h : Odd (σ 1 n)) :
    IsSquare n :=
  isSquare_of_factorization_even hn (factorization_even_of_odd_sigma hn hodd h)

/-- **Partial result towards Kanold's theorem.**  An odd superperfect number that is divisible
by `3` has an odd sum of divisors. -/
theorem odd_sigma_of_three_dvd {n : ℕ} (hodd : Odd n) (h : Superperfect n) (h3 : 3 ∣ n) :
    Odd (σ 1 n) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have hn1000 : 1000 < n := by
    by_contra hle
    exact no_odd_superperfect_le_1000 n (by omega) hodd h
  obtain ⟨j, hj⟩ := h3
  have hjdvd : j ∣ n := ⟨3, by omega⟩
  have h1 : n + j + 1 ≤ σ 1 n := add_add_one_le_sigma_of_dvd hjdvd (by omega) (by omega)
  obtain ⟨k, hk⟩ := hev
  have hkdvd : k ∣ σ 1 n := ⟨2, by omega⟩
  have h2 : σ 1 n + k + 1 ≤ σ 1 (σ 1 n) :=
    add_add_one_le_sigma_of_dvd hkdvd (by omega) (by omega)
  have h3 : σ 1 (σ 1 n) = 2 * n := h
  omega

/-- An odd superperfect number divisible by `3` is a perfect square. -/
theorem isSquare_of_three_dvd {n : ℕ} (hodd : Odd n) (h : Superperfect n) (h3 : 3 ∣ n) :
    IsSquare n :=
  isSquare_of_odd_of_odd_sigma (by rintro rfl; simp at hodd) hodd (odd_sigma_of_three_dvd hodd h h3)

/-! ### Main statement -/

/-- **Odd superperfect numbers (Brockian conjecture family).**

Whether an odd superperfect number exists is an open problem, so we record a Lean-checked
*conditional reduction*: the existence of an odd superperfect number is equivalent to the
existence of one satisfying a list of nontrivial extra constraints — it exceeds `1000`, it is
deficient, its sum of divisors is not a power of two, and if it is divisible by `3` then it is
a perfect square. -/
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

