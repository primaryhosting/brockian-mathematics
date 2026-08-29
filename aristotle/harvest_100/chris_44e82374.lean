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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked conditional reduction*: the set of Mersenne primes is infinite **if and only if**
the set of even perfect numbers is infinite.  Both implications go through a full formalisation
of the Euclid–Euler theorem, which is proved from scratch below.
-/

set_option autoImplicit false

namespace Brockian.MersennePerfect

open ArithmeticFunction Nat

/-- The sum-of-divisors function `σ₁`. -/
noncomputable def sigmaOne : ℕ → ℕ := fun n => ArithmeticFunction.sigma 1 n

theorem sigmaOne_apply (n : ℕ) : sigmaOne n = ∑ d ∈ n.divisors, d :=
  ArithmeticFunction.sigma_one_apply n

theorem sigmaOne_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigmaOne (a * b) = sigmaOne a * sigmaOne b :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

/-- The set of Mersenne primes, i.e. primes of the form `2 ^ k - 1`. -/
def MersennePrimes : Set ℕ := {q | q.Prime ∧ ∃ k, q = mersenne k}

/-- The set of even perfect numbers. -/
def EvenPerfects : Set ℕ := {n | Even n ∧ n.Perfect}

/-- The map sending a Mersenne prime `q = 2 ^ (j+1) - 1` to the perfect number `2 ^ j * q`. -/
def perfectOf (q : ℕ) : ℕ := (q + 1) / 2 * q

/-! ### Basic facts about `mersenne` -/

theorem mersenne_add_one (k : ℕ) : mersenne k + 1 = 2 ^ k := by
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  simp [mersenne, Nat.sub_add_cancel this]

theorem two_not_dvd_mersenne {k : ℕ} (hk : 1 ≤ k) : ¬ (2 ∣ mersenne k) := by
  intro h
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hm := mersenne_add_one k
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h2
  omega

theorem one_lt_mersenne {k : ℕ} (hk : 2 ≤ k) : 1 < mersenne k := by
  have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  simp only [mersenne]
  omega

theorem coprime_two_pow_mersenne (j : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Nat.Coprime (2 ^ j) (mersenne k) :=
  Nat.Coprime.pow_left _
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (two_not_dvd_mersenne hk))

/-! ### The sum-of-divisors computations -/

theorem geom_two_sum (k : ℕ) : ∑ x ∈ Finset.range (k + 1), 2 ^ x = mersenne (k + 1) := by
  induction k with
  | zero => simp [mersenne]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have e1 := mersenne_add_one (n + 1)
      have e2 := mersenne_add_one (n + 1 + 1)
      have e3 : (2 : ℕ) ^ (n + 1 + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) := by ring
      omega

theorem sigmaOne_two_pow (k : ℕ) : sigmaOne (2 ^ k) = mersenne (k + 1) := by
  have h := Nat.sum_divisors_prime_pow (f := fun x => x) (k := k) Nat.prime_two
  rw [sigmaOne_apply, h]
  simpa using geom_two_sum k

theorem sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = p + 1 := by
  rw [sigmaOne_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-! ### Euclid's direction -/

theorem perfect_two_pow_mul_mersenne {j : ℕ} (hp : (mersenne (j + 1)).Prime) :
    Nat.Perfect (2 ^ j * mersenne (j + 1)) := by
  have hq1 : 1 < mersenne (j + 1) := hp.one_lt
  have hpos : 0 < 2 ^ j * mersenne (j + 1) := by positivity
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigmaOne_apply,
    sigmaOne_mul_of_coprime (coprime_two_pow_mersenne j (k := j + 1) (by omega)),
    sigmaOne_two_pow, sigmaOne_prime hp, mersenne_add_one (j + 1)]
  have h2 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
  rw [h2]
  ring

theorem even_two_pow_mul_mersenne {j : ℕ} (hp : (mersenne (j + 1)).Prime) :
    Even (2 ^ j * mersenne (j + 1)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · norm_num [mersenne] at hp
  · exact (Nat.even_mul).2 (Or.inl ((Nat.even_pow' (by omega)).2 (by decide)))

/-! ### Euler's direction -/

/-- If the proper divisors of `m > 1` sum to a proper divisor `x` of `m`, then `x = 1` and
`m` is prime. -/
theorem sum_properDivisors_eq_of_dvd {m x : ℕ} (hm : 1 < m) (hx : x ∣ m) (hxm : x ≠ m)
    (hsum : ∑ i ∈ m.properDivisors, i = x) : x = 1 ∧ m.Prime := by
  have hx0 : 0 < x := Nat.pos_of_dvd_of_pos hx (by omega)
  have hxmem : x ∈ m.properDivisors := Nat.mem_properDivisors.2 ⟨hx, lt_of_le_of_ne
    (Nat.le_of_dvd (by omega) hx) hxm⟩
  have h1mem : 1 ∈ m.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.2 hm
  have hx1 : x = 1 := by
    by_contra hne
    have hsub : ({1, x} : Finset ℕ) ⊆ m.properDivisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> assumption
    have hle := Finset.sum_le_sum_of_subset (f := fun i => i) hsub
    rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ x), hsum] at hle
    omega
  subst hx1
  exact ⟨rfl, Nat.sum_properDivisors_eq_one_iff_prime.1 hsum⟩

theorem eq_two_pow_mul_mersenne_of_even_perfect {n : ℕ} (hev : Even n) (hperf : n.Perfect) :
    ∃ j : ℕ, (mersenne (j + 1)).Prime ∧ n = 2 ^ j * mersenne (j + 1) := by
  have hpos : 0 < n := hperf.2
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hpos
    · exact h
  -- `k ≥ 1` since `n` is even
  have hk : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [pow_zero, one_mul] at hev
    exact (Nat.not_even_iff_odd.2 hm) hev
  have hcop : Nat.Coprime (2 ^ k) m := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.prime_two.coprime_iff_not_dvd, Nat.odd_iff] at *
    omega
  have hsig : sigmaOne (2 ^ k * m) = 2 * (2 ^ k * m) := by
    rw [sigmaOne_apply, ← Nat.perfect_iff_sum_divisors_eq_two_mul hpos]
    exact hperf
  rw [sigmaOne_mul_of_coprime hcop, sigmaOne_two_pow] at hsig
  set q := mersenne (k + 1) with hq
  have hq1 : 1 < q := one_lt_mersenne (by omega)
  have hqa : q + 1 = 2 ^ (k + 1) := mersenne_add_one (k + 1)
  -- `q * σ m = (q+1) * m`
  have key : q * sigmaOne m = (q + 1) * m := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hqa, h2, hsig]
    ring
  -- hence `q ∣ m`
  have hqm : q ∣ m := by
    have hcop2 : Nat.Coprime q (q + 1) := by simp
    exact hcop2.dvd_of_dvd_mul_left ⟨sigmaOne m, key.symm⟩
  obtain ⟨x, rfl⟩ := hqm
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · simp at hmpos
    · exact h
  have hsm : sigmaOne (q * x) = (q + 1) * x := by
    have hqpos : 0 < q := by omega
    have h := key
    have h' : q * sigmaOne (q * x) = q * ((q + 1) * x) := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hqpos h'
  -- so the proper divisors of `m = q * x` sum to `x`
  have hprop : ∑ i ∈ (q * x).properDivisors, i = x := by
    have h1 : ∑ i ∈ (q * x).divisors, i = ∑ i ∈ (q * x).properDivisors, i + q * x :=
      Nat.sum_divisors_eq_sum_properDivisors_add_self
    rw [sigmaOne_apply] at hsm
    have h2 : (q + 1) * x = q * x + x := by ring
    omega
  have hxdvd : x ∣ q * x := dvd_mul_left x q
  have hxne : x ≠ q * x := by
    intro h
    have h1 : q * x = 1 * x := by omega
    have := Nat.eq_of_mul_eq_mul_right hx0 h1
    omega
  have hm1 : 1 < q * x := by
    have : 1 * 1 < q * x := Nat.mul_lt_mul_of_lt_of_le hq1 hx0 (by omega)
    omega
  obtain ⟨hx1, hprime⟩ := sum_properDivisors_eq_of_dvd hm1 hxdvd hxne hprop
  subst hx1
  rw [mul_one] at hprime
  exact ⟨k, hprime, by rw [mul_one]⟩

/-- **Euclid–Euler theorem**: `n` is an even perfect number iff `n = 2 ^ j * (2 ^ (j+1) - 1)`
for some `j` with `2 ^ (j+1) - 1` prime. -/
theorem even_perfect_iff {n : ℕ} :
    (Even n ∧ n.Perfect) ↔ ∃ j : ℕ, (mersenne (j + 1)).Prime ∧ n = 2 ^ j * mersenne (j + 1) := by
  constructor
  · rintro ⟨hev, hperf⟩
    exact eq_two_pow_mul_mersenne_of_even_perfect hev hperf
  · rintro ⟨j, hp, rfl⟩
    exact ⟨even_two_pow_mul_mersenne hp, perfect_two_pow_mul_mersenne hp⟩

/-! ### The correspondence between Mersenne primes and even perfect numbers -/

theorem mem_MersennePrimes_iff {q : ℕ} :
    q ∈ MersennePrimes ↔ ∃ j : ℕ, q = mersenne (j + 1) ∧ q.Prime := by
  constructor
  · rintro ⟨hp, k, rfl⟩
    rcases k with _ | j
    · norm_num [mersenne] at hp
    · exact ⟨j, rfl, hp⟩
  · rintro ⟨j, rfl, hp⟩
    exact ⟨hp, j + 1, rfl⟩

theorem perfectOf_mersenne (j : ℕ) :
    perfectOf (mersenne (j + 1)) = 2 ^ j * mersenne (j + 1) := by
  simp only [perfectOf]
  rw [mersenne_add_one (j + 1), pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem perfectOf_mem {q : ℕ} (hq : q ∈ MersennePrimes) : perfectOf q ∈ EvenPerfects := by
  obtain ⟨j, rfl, hp⟩ := mem_MersennePrimes_iff.1 hq
  rw [perfectOf_mersenne]
  exact ⟨even_two_pow_mul_mersenne hp, perfect_two_pow_mul_mersenne hp⟩

theorem two_mul_perfectOf {q : ℕ} (hq : q ∈ MersennePrimes) :
    2 * perfectOf q = q * (q + 1) := by
  obtain ⟨j, rfl, hp⟩ := mem_MersennePrimes_iff.1 hq
  rw [perfectOf_mersenne, mersenne_add_one (j + 1), pow_succ]
  ring

theorem perfectOf_injOn : Set.InjOn perfectOf MersennePrimes := by
  intro a ha b hb hab
  have h1 := two_mul_perfectOf ha
  have h2 := two_mul_perfectOf hb
  rw [hab, h2] at h1
  nlinarith [h1]

theorem EvenPerfects_subset_image : EvenPerfects ⊆ perfectOf '' MersennePrimes := by
  rintro n ⟨hev, hperf⟩
  obtain ⟨j, hp, rfl⟩ := eq_two_pow_mul_mersenne_of_even_perfect hev hperf
  exact ⟨mersenne (j + 1), ⟨hp, j + 1, rfl⟩, perfectOf_mersenne j⟩

/-! ### The main conditional result -/

/-- **Conditional reduction of the infinitude of Mersenne primes.**
The infinitude of Mersenne primes is an open problem; here we prove that it follows from (and,
by `evenPerfects_infinite_of_mersennePrimes_infinite`, is equivalent to) the infinitude of the
set of even perfect numbers. -/
theorem MersennePrimeInfinitude (h : EvenPerfects.Infinite) : MersennePrimes.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  exact h ((hfin.image perfectOf).subset EvenPerfects_subset_image)

/-- The converse direction: infinitely many Mersenne primes give infinitely many even perfect
numbers. -/
theorem evenPerfects_infinite_of_mersennePrimes_infinite (h : MersennePrimes.Infinite) :
    EvenPerfects.Infinite :=
  (h.image perfectOf_injOn).mono (by
    rintro n ⟨q, hq, rfl⟩
    exact perfectOf_mem hq)

/-- The infinitude of Mersenne primes is equivalent to the infinitude of even perfect numbers. -/
theorem mersennePrimes_infinite_iff : MersennePrimes.Infinite ↔ EvenPerfects.Infinite :=
  ⟨evenPerfects_infinite_of_mersennePrimes_infinite, MersennePrimeInfinitude⟩

/-! ### Two unconditional facts, showing the statements above are not vacuous -/

/-- The exponent of a Mersenne prime is itself prime. -/
theorem exponent_prime_of_mem_MersennePrimes {q : ℕ} (hq : q ∈ MersennePrimes) :
    ∃ p : ℕ, p.Prime ∧ q = mersenne p := by
  obtain ⟨hp, k, rfl⟩ := hq
  exact ⟨k, Nat.Prime.of_mersenne hp, rfl⟩

theorem three_mem_MersennePrimes : 3 ∈ MersennePrimes := ⟨by norm_num, 2, by norm_num [mersenne]⟩

theorem six_mem_EvenPerfects : 6 ∈ EvenPerfects := by
  have : (6 : ℕ) = perfectOf 3 := by norm_num [perfectOf]
  rw [this]
  exact perfectOf_mem three_mem_MersennePrimes

end Brockian.MersennePerfect

