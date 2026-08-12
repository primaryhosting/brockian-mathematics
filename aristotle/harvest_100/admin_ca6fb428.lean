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

/-
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module docstring because Lean 4
-- does not allow any command, including a module docstring, to precede the `import` lines.)

/-
## Overview

A positive integer `n` is *`k`-hyperperfect* (for `k ≥ 1`) when

  `n = 1 + k * (σ(n) - n - 1)`,

where `σ(n)` is the sum of all divisors of `n`; equivalently `σ(n) - n - 1` is the sum of
the divisors of `n` other than `1` and `n`.  Taking `k = 1` recovers the perfect numbers.
To avoid truncated natural subtraction the definition below is stated in the equivalent
subtraction-free form `n + k * (n + 1) = 1 + k * σ(n)`.

Whether there are infinitely many hyperperfect numbers is an open problem: already the case
`k = 1` is the (open) question of whether there are infinitely many perfect numbers.  What is
proved here is therefore a *conditional reduction* together with unconditional supporting
results:

* `Brockian.HyperperfectNumbers.isHyperperfect_mul` — an unconditional construction: whenever
  `k ≥ 1` and both `k + 1` and `k² + k + 1` are prime, the number `(k + 1)(k² + k + 1)` is
  `k`-hyperperfect.  (E.g. `k = 1, 2, 6` give `6`, `21`, `301`.)
* `Brockian.HyperperfectNumbers.HyperperfectInfinitude` — the main target: if there are
  arbitrarily large `k` with `k + 1` and `k² + k + 1` both prime (an instance of Bunyakovsky's
  conjecture), then the set of hyperperfect numbers is infinite.
* `Brockian.HyperperfectNumbers.hyperperfect_infinite_of_infinitely_many_mersenne_primes` — a
  second, independent conditional reduction: infinitely many Mersenne primes also imply
  infinitely many hyperperfect numbers (via the even perfect numbers, which are
  `1`-hyperperfect).
-/

import Mathlib

open scoped ArithmeticFunction.sigma
open ArithmeticFunction

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect: `k ≥ 1`, `n > 1` and `n = 1 + k * (σ n - n - 1)`, written in the
subtraction-free form `n + k * (n + 1) = 1 + k * σ n`. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ 1 < n ∧ n + k * (n + 1) = 1 + k * σ 1 n

/-- `n` is hyperperfect if it is `k`-hyperperfect for some `k ≥ 1`. -/
def Hyperperfect (n : ℕ) : Prop := ∃ k, IsHyperperfect k n

/-- The `k`-hyperperfect condition in its usual form with (truncated) subtraction. -/
theorem isHyperperfect_iff_sub {k n : ℕ} (hk : 0 < k) (hn : 1 < n) :
    IsHyperperfect k n ↔ n = 1 + k * (σ 1 n - n - 1) := by
  have hle : n + 1 ≤ σ 1 n := by
    rw [sigma_one_apply]
    have h1 : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Nat.one_mem_divisors.mpr (by omega)
      · exact Nat.mem_divisors_self _ (by omega)
    have := Finset.sum_le_sum_of_subset h1 (f := fun d => d)
    rwa [Finset.sum_pair (by omega : (1 : ℕ) ≠ n), Nat.add_comm 1 n] at this
  have hmul : k * (σ 1 n - n - 1) = k * σ 1 n - k * (n + 1) := by
    rw [Nat.mul_sub, Nat.mul_sub]; ring_nf; omega
  have hk' : k * (n + 1) ≤ k * σ 1 n := Nat.mul_le_mul_left _ hle
  constructor
  · rintro ⟨-, -, h⟩
    omega
  · intro h
    exact ⟨hk, hn, by omega⟩

/-- The sum of divisors of a prime. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors]
  simp [Finset.sum_pair hp.one_lt.ne, Nat.add_comm]

/-- **Unconditional construction.** If `k ≥ 1` and both `k + 1` and `k² + k + 1` are prime,
then `(k + 1) * (k² + k + 1)` is `k`-hyperperfect. -/
theorem isHyperperfect_mul {k : ℕ} (hk : 0 < k) (hp : Nat.Prime (k + 1))
    (hq : Nat.Prime (k ^ 2 + k + 1)) :
    IsHyperperfect k ((k + 1) * (k ^ 2 + k + 1)) := by
  have hne : k + 1 ≠ k ^ 2 + k + 1 := by nlinarith
  have hs : σ 1 ((k + 1) * (k ^ 2 + k + 1)) = (k + 1 + 1) * (k ^ 2 + k + 1 + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_primes hp hq).mpr hne),
      sigma_one_prime hp, sigma_one_prime hq]
  refine ⟨hk, by nlinarith, ?_⟩
  rw [hs]; ring

/-- `6` is a (`1`-)hyperperfect number. -/
theorem hyperperfect_six : Hyperperfect 6 :=
  ⟨1, by simpa using isHyperperfect_mul (k := 1) one_pos (by norm_num) (by norm_num)⟩

/-- `21` is a `2`-hyperperfect number. -/
theorem hyperperfect_twentyone : Hyperperfect 21 :=
  ⟨2, by simpa using isHyperperfect_mul (k := 2) two_pos (by norm_num) (by norm_num)⟩

/-- `301` is a `6`-hyperperfect number. -/
theorem hyperperfect_threehundredone : Hyperperfect 301 :=
  ⟨6, by simpa using isHyperperfect_mul (k := 6) (by norm_num) (by norm_num) (by norm_num)⟩

/-- **Main conditional theorem.**  If there are arbitrarily large `k` such that both `k + 1`
and `k ^ 2 + k + 1` are prime (a special case of Bunyakovsky's conjecture), then there are
infinitely many hyperperfect numbers. -/
theorem HyperperfectInfinitude
    (H : ∀ N : ℕ, ∃ k > N, Nat.Prime (k + 1) ∧ Nat.Prime (k ^ 2 + k + 1)) :
    {n : ℕ | Hyperperfect n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨k, hkN, hp, hq⟩ := H N
  refine ⟨(k + 1) * (k ^ 2 + k + 1), ⟨k, isHyperperfect_mul (by omega) hp hq⟩, ?_⟩
  calc N < k + 1 := by omega
    _ ≤ (k + 1) * (k ^ 2 + k + 1) := Nat.le_mul_of_pos_right _ (by positivity)

/-! ### A second conditional reduction, via Mersenne primes -/

theorem sum_range_two_pow (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; omega

theorem sigma_one_two_pow (m : ℕ) : σ 1 (2 ^ m) + 1 = 2 ^ (m + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two, sum_range_two_pow]

/-- **Euclid's construction is `1`-hyperperfect.** If `2 ^ (m + 1) - 1` is prime with `m ≥ 1`,
then `2 ^ m * (2 ^ (m + 1) - 1)` is a (perfect, hence) hyperperfect number. -/
theorem isHyperperfect_one_two_pow_mul_mersenne {m : ℕ} (hm : 0 < m)
    (hq : Nat.Prime (2 ^ (m + 1) - 1)) :
    IsHyperperfect 1 (2 ^ m * (2 ^ (m + 1) - 1)) := by
  set q := 2 ^ (m + 1) - 1 with hqdef
  have h2 : 2 ^ (m + 1) = 2 ^ m * 2 := by ring
  have hm2 : 4 ≤ 2 ^ m * 2 := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hq3 : 3 ≤ q := by omega
  have hcop : Nat.Coprime (2 ^ m) q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega))
  have hs : σ 1 (2 ^ m * q) = q * (q + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hq]
    have h3 := sigma_one_two_pow m
    have h4 : σ 1 (2 ^ m) = q := by omega
    rw [h4]
  refine ⟨one_pos, ?_, ?_⟩
  · nlinarith [Nat.one_le_two_pow (n := m)]
  · have hq1 : q + 1 = 2 ^ m * 2 := by omega
    have hdouble : q * (q + 1) = 2 * (2 ^ m * q) := by rw [hq1]; ring
    rw [hs]; omega

/-- **Second conditional reduction.** If there are infinitely many Mersenne primes, then there
are infinitely many hyperperfect numbers. -/
theorem hyperperfect_infinite_of_infinitely_many_mersenne_primes
    (H : ∀ N : ℕ, ∃ m > N, Nat.Prime (2 ^ (m + 1) - 1)) :
    {n : ℕ | Hyperperfect n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨m, hmN, hq⟩ := H N
  refine ⟨2 ^ m * (2 ^ (m + 1) - 1),
    ⟨1, isHyperperfect_one_two_pow_mul_mersenne (by omega) hq⟩, ?_⟩
  have h1 : N < 2 ^ m := lt_of_lt_of_le (by omega : N < m) Nat.lt_two_pow_self.le
  have h2 : 1 ≤ 2 ^ (m + 1) - 1 := by
    have : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc N < 2 ^ m := h1
    _ ≤ 2 ^ m * (2 ^ (m + 1) - 1) := Nat.le_mul_of_pos_right _ (by omega)

end Brockian.HyperperfectNumbers

