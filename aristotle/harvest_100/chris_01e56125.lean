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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-- The set of even perfect numbers. -/
def EvenPerfect : Set ℕ := {n | Even n ∧ Nat.Perfect n}

/-- The set of exponents `k` for which `2 ^ (k + 1) - 1` is a Mersenne prime. -/
def MersenneExp : Set ℕ := {k | Nat.Prime (mersenne (k + 1))}

/-- The Euclid map sending a Mersenne exponent `k` to the associated perfect number. -/
def euclidMap (k : ℕ) : ℕ := 2 ^ k * mersenne (k + 1)

lemma sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

lemma odd_mersenne_succ (k : ℕ) : Odd (mersenne (k + 1)) := by
  simp

/-- Euclid's direction: a Mersenne prime yields a perfect number. -/
lemma perfect_euclidMap {k : ℕ} (pr : Nat.Prime (mersenne (k + 1))) :
    Nat.Perfect (euclidMap k) := by
  have hpos : 0 < 2 ^ k * mersenne (k + 1) := by
    have := pr.pos
    positivity
  rw [euclidMap, Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime
      (((odd_mersenne_succ k).coprime_two_right).symm.pow_left _),
    sigma_one_two_pow]
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    (Nat.sum_properDivisors_eq_one_iff_prime).2 pr,
    show (1:ℕ) + mersenne (k + 1) = 2 ^ (k + 1) from by rw [add_comm]; exact succ_mersenne _]
  ring

lemma euclidMap_ne_zero_exp {k : ℕ} (pr : Nat.Prime (mersenne (k + 1))) : k ≠ 0 := by
  rintro rfl
  simp [mersenne, Nat.not_prime_one] at pr

lemma even_euclidMap {k : ℕ} (pr : Nat.Prime (mersenne (k + 1))) : Even (euclidMap k) := by
  have hk := euclidMap_ne_zero_exp pr
  simp [euclidMap, hk, parity_simps]

lemma exists_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬ Even m := by
  have h : FiniteMultiplicity 2 n := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  refine ⟨multiplicity 2 n, m, hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨j, rfl⟩
  exact ⟨j, by rw [pow_succ, mul_assoc, ← hm]⟩

/-- Euler's direction: every even perfect number arises from a Mersenne prime. -/
lemma exists_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = euclidMap k := by
  obtain ⟨k, m, rfl, hm⟩ := exists_two_pow_mul_odd perf.2
  have hpos := perf.2
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h] at hpos
    · exact h
  have hm2 : ¬ (2 ∣ m) := by rwa [even_iff_two_dvd] at hm
  have hModd : Odd (mersenne (k + 1)) := odd_mersenne_succ k
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ ((Nat.prime_two.coprime_iff_not_dvd).2 hm2)
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_two_pow] at perf
  have hdvd : mersenne (k + 1) ∣ m := by
    have h1 : mersenne (k + 1) ∣ 2 ^ (k + 1) * m := ⟨σ 1 m, by rw [perf]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left ((hModd.coprime_two_right).pow_right _) h1
  obtain ⟨j, rfl⟩ := hdvd
  have hMpos : 0 < mersenne (k + 1) := by
    rcases Nat.eq_zero_or_pos (mersenne (k + 1)) with h | h
    · simp [h] at hmpos
    · exact h
  have key : σ 1 (mersenne (k + 1) * j) = 2 ^ (k + 1) * j := by
    refine Nat.eq_of_mul_eq_mul_left hMpos ?_
    rw [perf]; ring
  have h2 : σ 1 (mersenne (k + 1) * j) = mersenne (k + 1) * j + j := by
    rw [key, ← succ_mersenne (k + 1)]; ring
  have h3 : ∑ i ∈ (mersenne (k + 1) * j).properDivisors, i = j := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self] at h2
    omega
  have hjdvd : (∑ i ∈ (mersenne (k + 1) * j).properDivisors, i) ∣ (mersenne (k + 1) * j) := by
    rw [h3]; exact Dvd.intro_left _ rfl
  rcases Nat.sum_properDivisors_dvd hjdvd with h | h
  · have hj1 : j = 1 := by omega
    subst hj1
    refine ⟨k, ?_, by simp [euclidMap]⟩
    rw [mul_one] at h
    exact (Nat.sum_properDivisors_eq_one_iff_prime).1 h
  · exfalso
    have hjm : j = mersenne (k + 1) * j := by omega
    have hM1 : mersenne (k + 1) = 1 := by
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h' | h'
        · simp [h'] at hmpos
        · exact h'
      nlinarith [hjm]
    have hk0 : k = 0 := by
      by_contra hk
      have hlt : mersenne 1 < mersenne (k + 1) := mersenne_lt_mersenne.2 (by omega)
      rw [hM1] at hlt
      simp [mersenne] at hlt
    subst hk0
    rw [hM1] at ev
    simp at ev
    exact hm (by simpa [hM1] using ev)

/-- The Euclid–Euler characterisation of even perfect numbers. -/
theorem even_perfect_iff {n : ℕ} :
    n ∈ EvenPerfect ↔ ∃ k ∈ MersenneExp, n = euclidMap k := by
  constructor
  · rintro ⟨ev, perf⟩
    obtain ⟨k, pr, hk⟩ := exists_mersenne_of_even_perfect ev perf
    exact ⟨k, pr, hk⟩
  · rintro ⟨k, pr, rfl⟩
    exact ⟨even_euclidMap pr, perfect_euclidMap pr⟩

lemma strictMono_euclidMap : StrictMono euclidMap := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 : mersenne (k + 1) < mersenne (k + 1 + 1) := mersenne_lt_mersenne.2 (by omega)
  have h2 : (2:ℕ) ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 0 < mersenne (k + 1) := mersenne_pos.2 (by omega)
  have : (2:ℕ) ^ k * mersenne (k + 1) < 2 ^ (k + 1) * mersenne (k + 1 + 1) :=
    Nat.mul_lt_mul_of_le_of_lt h2 h1 (by positivity)
  simpa [euclidMap] using this

lemma image_euclidMap : euclidMap '' MersenneExp = EvenPerfect := by
  ext n
  simp only [Set.mem_image, even_perfect_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

/-- **Even Perfect Infinitude (conditional reduction).**  There are infinitely many even
perfect numbers if and only if there are infinitely many Mersenne primes. -/
theorem EvenPerfectInfinitude : EvenPerfect.Infinite ↔ MersenneExp.Infinite := by
  rw [← image_euclidMap, Set.infinite_image_iff strictMono_euclidMap.injective.injOn]

/-- The set of Mersenne primes, indexed by their (necessarily prime) exponent. -/
def MersennePrimeExp : Set ℕ := {p | p.Prime ∧ (mersenne p).Prime}

lemma image_succ_mersenneExp : (fun k => k + 1) '' MersenneExp = MersennePrimeExp := by
  ext p
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Nat.Prime.of_mersenne hk, hk⟩
  · rintro ⟨hp, hmp⟩
    have hp1 : p - 1 + 1 = p := by have := hp.two_le; omega
    refine ⟨p - 1, ?_, by simpa using hp1⟩
    simpa [MersenneExp, hp1] using hmp

/-- Restatement of the reduction: there are infinitely many even perfect numbers iff there are
infinitely many Mersenne primes `2 ^ p - 1` (with `p` prime). -/
theorem evenPerfectInfinitude_iff_mersennePrimes :
    EvenPerfect.Infinite ↔ MersennePrimeExp.Infinite := by
  rw [EvenPerfectInfinitude, ← image_succ_mersenneExp,
    Set.infinite_image_iff (Function.Injective.injOn fun a b h => by omega)]

/-- The first four even perfect numbers. -/
lemma evenPerfect_examples : ({6, 28, 496, 8128} : Set ℕ) ⊆ EvenPerfect := by
  intro n hn
  have H : ∀ k : ℕ, Nat.Prime (mersenne (k + 1)) → euclidMap k ∈ EvenPerfect :=
    fun k hk => even_perfect_iff.2 ⟨k, hk, rfl⟩
  rcases hn with rfl | rfl | rfl | rfl
  · simpa [euclidMap, mersenne] using H 1 (by norm_num [mersenne])
  · simpa [euclidMap, mersenne] using H 2 (by norm_num [mersenne])
  · simpa [euclidMap, mersenne] using H 4 (by norm_num [mersenne])
  · simpa [euclidMap, mersenne] using H 6 (by norm_num [mersenne])

end Brockian.MersennePerfect

