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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` form a *betrothed* (or *quasi-amicable*) pair when the sum of
the divisors of each, excluding `1` and the number itself, equals the other number; equivalently
`σ m = σ n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- The set of numbers belonging to some betrothed pair. -/
def betrothedNumbers : Set ℕ := {m | ∃ n, IsBetrothedPair m n}

theorem IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hmn, h1, h2⟩ := h
  refine ⟨hn, hm, hmn.symm, ?_, ?_⟩ <;> omega

theorem mem_betrothedNumbers {m n : ℕ} (h : IsBetrothedPair m n) : m ∈ betrothedNumbers :=
  ⟨n, h⟩

/-! ### Basic structure of betrothed pairs -/

/-- No member of a betrothed pair equals `1`. -/
theorem IsBetrothedPair.ne_one {m n : ℕ} (h : IsBetrothedPair m n) : m ≠ 1 := by
  obtain ⟨_, hn, _, h1, _⟩ := h
  rintro rfl
  rw [(sigma_eq_one_iff 1 1).2 rfl] at h1
  omega

/-- No member of a betrothed pair is prime. -/
theorem IsBetrothedPair.not_prime {m n : ℕ} (h : IsBetrothedPair m n) : ¬ m.Prime := by
  obtain ⟨_, hn, _, h1, _⟩ := h
  intro hp
  have hm : σ 1 m = m + 1 := by
    have := sigma_one_apply_prime_pow (p := m) (i := 1) hp
    simp [Finset.sum_range_succ] at this
    simpa [add_comm] using this
  omega

/-! ### Values of `σ` used below -/

theorem sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      ring_nf
      omega

theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simp [Finset.sum_range_succ] at this
  simpa [add_comm] using this

theorem sigma_one_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_two_pow, sigma_one_prime hp]

/-! ### An unconditional partial result: same-parity pairs

If a betrothed pair `(m, n)` has `m ≡ n (mod 2)`, then `σ m = σ n = m + n + 1` is odd, which
forces every odd prime to occur to an even power in `m` and in `n`; equivalently, `m` and `n`
are each a square or twice a square.  No such pair is known. -/

/-- If an odd prime occurs to an odd power in `m`, then `σ m` is even. -/
theorem even_sigma_one_of_odd_factorization {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ m) (hodd : Odd (m.factorization p)) : Even (σ 1 m) := by
  have hfac : σ 1 m = m.factorization.prod fun q k => σ 1 (q ^ k) :=
    isMultiplicative_sigma.multiplicative_factorization _ hm
  have hmem : p ∈ m.factorization.support := by
    rw [Nat.support_factorization]
    exact Nat.mem_primeFactors.2 ⟨hp, hpm, hm⟩
  have hdvd : σ 1 (p ^ m.factorization p) ∣ σ 1 m := by
    rw [hfac]; exact Finset.dvd_prod_of_mem _ hmem
  have heven : Even (σ 1 (p ^ m.factorization p)) := by
    rw [sigma_one_apply_prime_pow hp]
    have hone : ∀ j ∈ Finset.range (m.factorization p + 1), p ^ j % 2 = 1 := fun j _ =>
      Nat.odd_iff.1 (hp.odd_of_ne_two hp2).pow
    rw [Nat.even_iff, Finset.sum_nat_mod, Finset.sum_congr rfl hone]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    obtain ⟨t, ht⟩ := hodd
    omega
  exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 heven).trans hdvd)

/-- In a betrothed pair whose two members have the same parity, every odd prime occurs to an even
power (so each member is a square or twice a square). -/
theorem IsBetrothedPair.even_factorization_of_same_parity {m n : ℕ} (h : IsBetrothedPair m n)
    (hpar : m % 2 = n % 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Even (m.factorization p) := by
  obtain ⟨hm, -, -, h1, -⟩ := h
  by_cases hpm : p ∣ m
  · by_contra hcon
    have hoddexp : Odd (m.factorization p) := Nat.odd_iff.2 (Nat.not_even_iff.1 hcon)
    have := even_sigma_one_of_odd_factorization hm.ne' hp hp2 hpm hoddexp
    rw [h1, Nat.even_iff] at this
    omega
  · simp [Nat.factorization_eq_zero_of_not_dvd hpm]

/-! ### A Thabit-style criterion

If `n = 2 ^ k * p` with `p` an odd prime, then the only possible betrothed partner of `n` is
`m = σ n - n - 1 = (2 ^ k - 1) * (p + 2)`, and the pair works as soon as `σ m = σ n`.  This
criterion produces, e.g., the pairs `(75, 48)`, `(1575, 1648)` and `(5775, 6128)`. -/
/-- The arithmetic identity behind the criterion. -/
theorem sigma_criterion_key (k p : ℕ) :
    (2 ^ k - 1) * (p + 2) + 2 ^ k * p + 1 = (2 ^ (k + 1) - 1) * (p + 1) := by
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  have h3 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  zify [h1, h3]
  ring

theorem betrothed_of_sigma_criterion {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : σ 1 ((2 ^ k - 1) * (p + 2)) = (2 ^ (k + 1) - 1) * (p + 1)) :
    IsBetrothedPair ((2 ^ k - 1) * (p + 2)) (2 ^ k * p) := by
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h3 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hppos : 0 < p := hp.pos
  have key := sigma_criterion_key k p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (by omega) (by omega)
  · exact Nat.mul_pos (by omega) hppos
  · -- the two numbers have different parities
    have hodd : Odd ((2 ^ k - 1) * (p + 2)) := by
      refine Odd.mul ?_ ?_
      · exact Nat.Even.sub_odd h1 ((Nat.even_pow' (by omega)).2 even_two) odd_one
      · exact (hp.odd_of_ne_two hp2).add_even (by decide)
    have heven : Even (2 ^ k * p) :=
      Even.mul_right ((Nat.even_pow' (by omega)).2 even_two) p
    intro hEq
    rw [hEq] at hodd
    exact (Nat.not_odd_iff_even.2 heven) hodd
  · rw [h, key]
  · rw [sigma_one_two_pow_mul_prime hp hp2, key]

/-- Conversely, a number of the shape `2 ^ k * p` (`k ≥ 1`, `p` an odd prime) has at most one
possible betrothed partner, namely `(2 ^ k - 1) * (p + 2)`. -/
theorem eq_of_isBetrothedPair_two_pow_mul_prime {k p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsBetrothedPair m (2 ^ k * p)) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨-, -, -, -, h2⟩ := h
  rw [sigma_one_two_pow_mul_prime hp hp2] at h2
  have key := sigma_criterion_key k p
  omega

/-- For `n = 2 ^ k * p` with `k ≥ 1` and `p` an odd prime, `n` belongs to a betrothed pair exactly
when the Thabit-style criterion holds. -/
theorem isBetrothedPair_two_pow_mul_prime_iff {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ m, IsBetrothedPair m (2 ^ k * p)) ↔
      σ 1 ((2 ^ k - 1) * (p + 2)) = (2 ^ (k + 1) - 1) * (p + 1) := by
  constructor
  · rintro ⟨m, hm⟩
    have hme : m = (2 ^ k - 1) * (p + 2) := eq_of_isBetrothedPair_two_pow_mul_prime hp hp2 hm
    obtain ⟨-, -, -, h1, -⟩ := hm
    have key := sigma_criterion_key k p
    rw [hme] at h1
    omega
  · intro h
    exact ⟨_, betrothed_of_sigma_criterion hk hp hp2 h⟩

/-! ### Concrete betrothed pairs -/

/-- `(48, 75)` is a betrothed pair: `σ 48 = σ 75 = 124 = 48 + 75 + 1`. -/
theorem betrothed_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- `(140, 195)` is a betrothed pair. -/
theorem betrothed_140_195 : IsBetrothedPair 140 195 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

set_option maxRecDepth 40000 in
/-- `(1050, 1925)` is a betrothed pair. -/
theorem betrothed_1050_1925 : IsBetrothedPair 1050 1925 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- The criterion is not vacuous: with `k = 4`, `p = 3` it produces the pair `(75, 48)`. -/
theorem betrothed_75_48_of_criterion : IsBetrothedPair 75 48 := by
  have := betrothed_of_sigma_criterion (k := 4) (p := 3) (by norm_num) (by norm_num)
    (by norm_num) (by decide)
  norm_num at this
  exact this

set_option maxRecDepth 40000 in
/-- With `k = 4`, `p = 103` the criterion produces the pair `(1575, 1648)`. -/
theorem betrothed_1575_1648_of_criterion : IsBetrothedPair 1575 1648 := by
  have := betrothed_of_sigma_criterion (k := 4) (p := 103) (by norm_num) (by norm_num)
    (by norm_num) (by decide)
  norm_num at this
  exact this

/-! ### Infinitude -/

/-- Unboundedness of the set of betrothed numbers is equivalent to its infinitude. -/
theorem betrothedNumbers_infinite_iff :
    betrothedNumbers.Infinite ↔ ∀ N : ℕ, ∃ m ∈ betrothedNumbers, N < m := by
  constructor
  · intro h N
    obtain ⟨m, hm, hmN⟩ := h.exists_gt N
    exact ⟨m, hm, hmN⟩
  · exact Set.infinite_of_forall_exists_gt

/-- **Betrothed infinitude (conditional).**  Whether there are infinitely many betrothed
(quasi-amicable) pairs is an open problem.  The following is a Lean-checked reduction: if the
Thabit-style criterion `σ ((2 ^ k - 1) * (p + 2)) = (2 ^ (k + 1) - 1) * (p + 1)` has solutions
with `k ≥ 1`, `p` an odd prime and `(2 ^ k - 1) * (p + 2)` arbitrarily large, then there are
infinitely many betrothed numbers, hence infinitely many betrothed pairs. -/
theorem BetrothedInfinitude
    (H : ∀ N : ℕ, ∃ k p : ℕ, 1 ≤ k ∧ p.Prime ∧ p ≠ 2 ∧ N < (2 ^ k - 1) * (p + 2) ∧
      σ 1 ((2 ^ k - 1) * (p + 2)) = (2 ^ (k + 1) - 1) * (p + 1)) :
    betrothedNumbers.Infinite := by
  refine betrothedNumbers_infinite_iff.2 fun N => ?_
  obtain ⟨k, p, hk, hp, hp2, hlt, hsig⟩ := H N
  exact ⟨_, mem_betrothedNumbers (betrothed_of_sigma_criterion hk hp hp2 hsig), hlt⟩

end Brockian.BetrothedNumbers

