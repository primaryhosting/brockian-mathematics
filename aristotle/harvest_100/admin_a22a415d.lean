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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module doc comment `/-! ... -/`,
-- so the header is repeated verbatim as a module docstring just below the import.)

import Mathlib

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so we do not prove it
outright.  Instead we give a Lean-checked *equivalent reformulation*: the set of
exponents `p` for which `2 ^ p - 1` is prime is infinite **if and only if** the set of
even perfect numbers is infinite.  The equivalence comes from the Euclid–Euler
theorem, which is reproved here (following the Mathlib archive development of the
Euclid–Euler theorem) so that the file depends only on `Mathlib` itself.

We also record the contrapositive form: there are only finitely many Mersenne primes
iff there are only finitely many even perfect numbers.
-/

namespace Brockian

namespace MersennePerfect

open ArithmeticFunction Finset

open scoped sigma

/-! ### The Euclid–Euler theorem -/

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
    Even (2 ^ k * mersenne (k + 1)) := by simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- **Perfect Number Theorem**: Euler's theorem that even perfect numbers can be factored as a
power of two times a Mersenne prime. -/
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

/-- The Euclid–Euler theorem characterizing even perfect numbers. -/
theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  · rintro ⟨k, pr, rfl⟩
    exact ⟨even_two_pow_mul_mersenne_of_prime k pr, perfect_two_pow_mul_mersenne_of_prime k pr⟩

/-! ### The two sets in play -/

/-- The set of exponents `p` such that the Mersenne number `2 ^ p - 1` is prime. -/
def MersenneExponents : Set ℕ := {p : ℕ | Nat.Prime (mersenne p)}

/-- The set of even perfect numbers. -/
def EvenPerfects : Set ℕ := {n : ℕ | Even n ∧ Nat.Perfect n}

/-- The Euclid–Euler map sending an exponent `p` to `2 ^ (p - 1) * (2 ^ p - 1)`. -/
def euclidEuler (p : ℕ) : ℕ := 2 ^ (p - 1) * mersenne p

/-- Every exponent of a Mersenne prime is positive. -/
theorem pos_of_mem_mersenneExponents {p : ℕ} (hp : p ∈ MersenneExponents) : 0 < p := by
  rcases Nat.eq_zero_or_pos p with rfl | h
  · simp [MersenneExponents, mersenne, Nat.not_prime_zero] at hp
  · exact h

/-- The Euclid–Euler map is strictly monotone on positive exponents. -/
theorem euclidEuler_lt_euclidEuler {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    euclidEuler p < euclidEuler q := by
  have h1 : (2 : ℕ) ^ (p - 1) ≤ 2 ^ (q - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : mersenne p < mersenne q := by
    have hlt : (2 : ℕ) ^ p < 2 ^ q := Nat.pow_lt_pow_right (by norm_num) hpq
    have h2p : 1 ≤ (2 : ℕ) ^ p := Nat.one_le_two_pow
    simp only [mersenne]
    omega
  have hmp : 0 < mersenne p := by
    have h2p : (2 : ℕ) ^ 1 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    simp only [mersenne]
    omega
  exact Nat.mul_lt_mul_of_le_of_lt h1 h2 (by positivity)

/-- The Euclid–Euler map is injective on the set of Mersenne exponents. -/
theorem injOn_euclidEuler : Set.InjOn euclidEuler MersenneExponents := by
  intro p hp q hq hpq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hpq (Nat.ne_of_lt
      (euclidEuler_lt_euclidEuler (pos_of_mem_mersenneExponents hp) h))
  · exact absurd hpq.symm (Nat.ne_of_lt
      (euclidEuler_lt_euclidEuler (pos_of_mem_mersenneExponents hq) h))

/-- The even perfect numbers are exactly the images of Mersenne exponents under the
Euclid–Euler map. -/
theorem image_euclidEuler : euclidEuler '' MersenneExponents = EvenPerfects := by
  ext n
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 :=
      ⟨p - 1, by have := pos_of_mem_mersenneExponents hp; omega⟩
    have hpr : Nat.Prime (mersenne (k + 1)) := hp
    refine even_and_perfect_iff.mpr ⟨k, hpr, ?_⟩
    simp [euclidEuler]
  · rintro ⟨hev, hperf⟩
    obtain ⟨k, hpr, rfl⟩ := even_and_perfect_iff.mp ⟨hev, hperf⟩
    exact ⟨k + 1, hpr, by simp [euclidEuler]⟩

/-! ### Main result -/

/-- **Reformulation of the Mersenne prime infinitude conjecture.**

There are infinitely many Mersenne primes (i.e. infinitely many exponents `p` with
`2 ^ p - 1` prime) if and only if there are infinitely many even perfect numbers.

The infinitude itself is an open problem; this is a Lean-checked equivalent
reformulation, obtained from the Euclid–Euler theorem. -/
theorem MersennePrimeInfinitude :
    MersenneExponents.Infinite ↔ EvenPerfects.Infinite := by
  constructor
  · intro h
    rw [← image_euclidEuler]
    exact h.image injOn_euclidEuler
  · intro h
    rw [← image_euclidEuler] at h
    exact h.of_image euclidEuler

/-- Contrapositive form: there are only finitely many Mersenne primes iff there are only
finitely many even perfect numbers. -/
theorem mersennePrimeFinite_iff_evenPerfectFinite :
    MersenneExponents.Finite ↔ EvenPerfects.Finite := by
  simpa [← Set.not_infinite, not_iff_not] using MersennePrimeInfinitude

/-! ### Sanity checks (non-vacuity) -/

example : 2 ∈ MersenneExponents := by
  norm_num [MersenneExponents, mersenne]

example : 3 ∈ MersenneExponents := by
  norm_num [MersenneExponents, mersenne]

example : (6 : ℕ) ∈ EvenPerfects := by
  have : euclidEuler 2 = 6 := by norm_num [euclidEuler, mersenne]
  rw [← this, ← image_euclidEuler]
  exact ⟨2, by norm_num [MersenneExponents, mersenne], rfl⟩

example : (28 : ℕ) ∈ EvenPerfects := by
  have : euclidEuler 3 = 28 := by norm_num [euclidEuler, mersenne]
  rw [← this, ← image_euclidEuler]
  exact ⟨3, by norm_num [MersenneExponents, mersenne], rfl⟩

end MersennePerfect

end Brockian

