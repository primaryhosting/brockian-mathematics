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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-! ## The Euclid–Euler theorem

The proofs in this section follow the classical Euclid–Euler argument (as formalized in
`Archive/Wiedijk100Theorems/PerfectNumbers.lean` in mathlib, which is not available as an
import here). -/

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- Euclid's theorem that Mersenne primes induce perfect numbers. -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  refine ⟨multiplicity 2 n, m, hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- Euler's theorem that even perfect numbers can be factored as a power of two times a
Mersenne prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose! hm
    simp [hm]

/-- The Euclid–Euler characterization of even perfect numbers. -/
theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔
      ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  · rintro ⟨k, pr, rfl⟩
    exact ⟨even_two_pow_mul_mersenne_of_prime k pr, perfect_two_pow_mul_mersenne_of_prime k pr⟩

/-! ## The sets involved -/

/-- The set of even perfect natural numbers. -/
def EvenPerfects : Set ℕ := {n : ℕ | Even n ∧ Nat.Perfect n}

/-- The set of Mersenne exponents, i.e. those `p` for which `mersenne p = 2 ^ p - 1` is prime.
(Such a `p` is automatically prime.) -/
def MersenneExponents : Set ℕ := {p : ℕ | (mersenne p).Prime}

/-- An even perfect number `2 ^ k * mersenne (k + 1)` is at most `2 ^ (2 * k + 1)`. -/
theorem euclid_number_le (k : ℕ) : 2 ^ k * mersenne (k + 1) ≤ 2 ^ (2 * k + 1) := by
  have h : mersenne (k + 1) ≤ 2 ^ (k + 1) := by
    simp [mersenne]
  calc 2 ^ k * mersenne (k + 1) ≤ 2 ^ k * 2 ^ (k + 1) := Nat.mul_le_mul_left _ h
    _ = 2 ^ (2 * k + 1) := by rw [← pow_add]; ring_nf

/-- An even perfect number `2 ^ k * mersenne (k + 1)` is at least `k + 1`. -/
theorem le_euclid_number (k : ℕ) : k + 1 ≤ 2 ^ k * mersenne (k + 1) := by
  have h1 : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have h2 : 1 ≤ mersenne (k + 1) := by
    have : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [mersenne]
    omega
  calc k + 1 ≤ 2 ^ k := h1
    _ = 2 ^ k * 1 := (mul_one _).symm
    _ ≤ 2 ^ k * mersenne (k + 1) := Nat.mul_le_mul_left _ h2

/-! ## Main result -/

/-- **Even Perfect Infinitude.**  There are infinitely many even perfect numbers if and only if
there are infinitely many Mersenne primes.  (Whether either side actually holds is a famous open
problem; this theorem is the unconditional reduction of one to the other, and is proved via the
Euclid–Euler theorem.) -/
theorem EvenPerfectInfinitude : EvenPerfects.Infinite ↔ MersenneExponents.Infinite := by
  constructor
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hn, hgt⟩ := h.exists_gt (2 ^ (2 * N + 1))
    obtain ⟨k, pr, rfl⟩ := even_and_perfect_iff.1 hn
    refine ⟨k + 1, pr, ?_⟩
    have hle := euclid_number_le k
    have h2 : 2 ^ (2 * N + 1) < 2 ^ (2 * k + 1) := lt_of_lt_of_le hgt hle
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 h2
    omega
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨p, hp, hgt⟩ := h.exists_gt N
    have hp' : (mersenne p).Prime := hp
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact absurd hp' (by decide)
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    refine ⟨2 ^ k * mersenne (k + 1), even_and_perfect_iff.2 ⟨k, hp', rfl⟩, ?_⟩
    have := le_euclid_number k
    omega

/-! ## Sanity checks: both sides are nonempty -/

/-- `6` is an even perfect number. -/
theorem six_mem_evenPerfects : (6 : ℕ) ∈ EvenPerfects := by
  refine ⟨by decide, ?_⟩
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (by norm_num)]
  decide

/-- `28` is an even perfect number. -/
theorem twentyEight_mem_evenPerfects : (28 : ℕ) ∈ EvenPerfects := by
  refine ⟨by decide, ?_⟩
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (by norm_num)]
  decide

/-- `2` is a Mersenne exponent: `2 ^ 2 - 1 = 3` is prime. -/
theorem two_mem_mersenneExponents : (2 : ℕ) ∈ MersenneExponents := by
  show (mersenne 2).Prime
  norm_num [mersenne]

end MersennePerfect
end Brockian

