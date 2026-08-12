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
-- (The header above is a plain block comment rather than a `/-!` module docstring:
-- Lean 4 requires `import` commands to precede every other command, including module
-- docstrings.  The same text is repeated as the module docstring after the import.)

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

set_option maxHeartbeats 2000000

namespace Brockian.BetrothedNumbers

open Finset

/-- The classical divisor sum `σ₁ n = ∑_{d ∣ n} d`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

lemma sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = ArithmeticFunction.sigma 1 n := by
  simp [sigmaOne, ArithmeticFunction.sigma_one_apply]

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair when they are distinct positive
integers each of whose divisor sum equals `m + n + 1`; equivalently, each is the sum of the
nontrivial proper divisors (excluding `1`) of the other. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- The candidate betrothed partner of `m`: the sum of the proper divisors of `m` other
than `1`. -/
def partner (m : ℕ) : ℕ := sigmaOne m - m - 1

/-- One-variable form of betrothedness: `m` belongs to a betrothed pair. -/
def IsBetrothed (m : ℕ) : Prop :=
  0 < m ∧ 0 < partner m ∧ partner m ≠ m ∧ sigmaOne (partner m) = sigmaOne m

/-! ## Basic structure -/

lemma IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hmn, h1, h2⟩ := h
  refine ⟨hn, hm, hmn.symm, ?_, ?_⟩ <;> omega

/-- In a betrothed pair the partner is uniquely determined. -/
lemma IsBetrothedPair.eq_partner {m n : ℕ} (h : IsBetrothedPair m n) : n = partner m := by
  obtain ⟨-, -, -, h1, -⟩ := h
  simp only [partner, h1]; omega

/-- The two members of a betrothed pair have the same divisor sum. -/
lemma IsBetrothedPair.sigmaOne_eq {m n : ℕ} (h : IsBetrothedPair m n) :
    sigmaOne m = sigmaOne n := by
  obtain ⟨-, -, -, h1, h2⟩ := h; omega

/-- The one-variable condition characterises membership in a betrothed pair. -/
theorem isBetrothed_iff (m : ℕ) : IsBetrothed m ↔ ∃ n, IsBetrothedPair m n := by
  constructor
  · rintro ⟨hm, hp, hne, hs⟩
    refine ⟨partner m, hm, hp, fun h => hne h.symm, ?_, ?_⟩
    · have : m + 1 < sigmaOne m := by
        simp only [partner] at hp; omega
      simp only [partner]; omega
    · have : m + 1 < sigmaOne m := by
        simp only [partner] at hp; omega
      rw [hs]; simp only [partner]; omega
  · rintro ⟨n, h⟩
    have hn := h.eq_partner
    obtain ⟨hm, hpos, hne, h1, h2⟩ := h
    subst hn
    exact ⟨hm, hpos, fun hh => hne hh.symm, by omega⟩

/-! ## Concrete betrothed pairs -/

theorem betrothed_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> (unfold sigmaOne; decide)

theorem betrothed_140_195 : IsBetrothedPair 140 195 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> (unfold sigmaOne; decide)

theorem betrothed_1050_1925 : IsBetrothedPair 1050 1925 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> (unfold sigmaOne; decide)

theorem betrothed_1575_1648 : IsBetrothedPair 1575 1648 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> (unfold sigmaOne; decide)

theorem betrothed_2024_2295 : IsBetrothedPair 2024 2295 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> (unfold sigmaOne; decide)

/-- There is at least one betrothed pair. -/
theorem exists_betrothedPair : ∃ m n : ℕ, IsBetrothedPair m n :=
  ⟨48, 75, betrothed_48_75⟩

set_option maxRecDepth 1000000 in
/-- Exhaustive verification below `300`: the only betrothed numbers `m < 300` are the members
of the pairs `(48, 75)` and `(140, 195)`. -/
theorem isBetrothed_lt_300 (m : ℕ) (hm : m < 300) :
    IsBetrothed m ↔ (m = 48 ∨ m = 75 ∨ m = 140 ∨ m = 195) := by
  revert m
  simp only [IsBetrothed, partner, sigmaOne]
  decide

/-! ## Elementary exclusions -/

lemma sigmaOne_one : sigmaOne 1 = 1 := by unfold sigmaOne; decide

lemma sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = p + 1 := by
  rw [sigmaOne, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-- No member of a betrothed pair equals `1`. -/
lemma IsBetrothedPair.ne_one {m n : ℕ} (h : IsBetrothedPair m n) : m ≠ 1 := by
  rintro rfl
  obtain ⟨-, hn, -, h1, -⟩ := h
  rw [sigmaOne_one] at h1
  omega

/-- No member of a betrothed pair is prime. -/
lemma IsBetrothedPair.not_prime {m n : ℕ} (h : IsBetrothedPair m n) : ¬ m.Prime := by
  intro hp
  obtain ⟨-, hn, -, h1, -⟩ := h
  rw [sigmaOne_prime hp] at h1
  omega

/-- Both members of a betrothed pair are composite. -/
lemma IsBetrothedPair.not_prime_right {m n : ℕ} (h : IsBetrothedPair m n) : ¬ n.Prime :=
  h.symm.not_prime

/-! ## Parity of the divisor sum, and the parity structure of betrothed pairs -/

lemma sigmaOne_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    sigmaOne (p ^ e) = ∑ i ∈ Finset.range (e + 1), p ^ i := by
  rw [sigmaOne_eq_sigma, ArithmeticFunction.sigma_one_apply_prime_pow hp]

lemma odd_sigmaOne_two_pow (e : ℕ) : Odd (sigmaOne (2 ^ e)) := by
  rw [sigmaOne_prime_pow Nat.prime_two]
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Finset.sum_range_succ]
      exact ih.add_even (Nat.even_pow.2 ⟨even_two, by omega⟩)

lemma odd_sigmaOne_prime_pow_iff {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Odd (sigmaOne (p ^ e)) ↔ Even e := by
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  rw [sigmaOne_prime_pow hp, Nat.odd_iff, Finset.sum_nat_mod]
  simp [Nat.pow_mod, hodd, Nat.even_iff]
  omega

lemma sigmaOne_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
    sigmaOne n = n.factorization.prod fun p k => sigmaOne (p ^ k) := by
  simp only [sigmaOne_eq_sigma]
  exact ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn

/-- `σ₁ n` is odd exactly when every odd prime occurs in `n` to an even power. -/
theorem odd_sigmaOne_iff_even_odd_exponents {n : ℕ} (hn : n ≠ 0) :
    Odd (sigmaOne n) ↔ ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p) := by
  rw [sigmaOne_eq_prod_factorization hn, ← Nat.not_even_iff_odd, even_iff_two_dvd,
    Finsupp.prod, Nat.support_factorization, Nat.prime_two.prime.dvd_finset_prod_iff]
  push_neg
  constructor
  · intro h p hp hp2
    have h2 := h p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd] at h2
    exact (odd_sigmaOne_prime_pow_iff hpp hp2).1 h2
  · intro h p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    by_cases hp2 : p = 2
    · subst hp2; exact odd_sigmaOne_two_pow _
    · exact (odd_sigmaOne_prime_pow_iff hpp hp2).2 (h p hp hp2)

/-- If `σ₁ n` is odd then `n` is a power of two times a square (equivalently, `n` is a
square or twice a square). -/
theorem eq_two_pow_mul_sq_of_odd_sigmaOne {n : ℕ} (hn : n ≠ 0) (h : Odd (sigmaOne n)) :
    ∃ a k : ℕ, 0 < k ∧ n = 2 ^ a * k ^ 2 := by
  classical
  have hall := (odd_sigmaOne_iff_even_odd_exponents hn).1 h
  refine ⟨n.factorization 2, ∏ p ∈ n.primeFactors.erase 2, p ^ (n.factorization p / 2), ?_, ?_⟩
  · exact Finset.prod_pos fun p hp =>
      pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) _
  · have hprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using Nat.factorization_prod_pow_eq_self hn
    have hsq : (∏ p ∈ n.primeFactors.erase 2, p ^ (n.factorization p / 2)) ^ 2
        = ∏ p ∈ n.primeFactors.erase 2, p ^ n.factorization p := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun p hp => ?_
      have he : Even (n.factorization p) :=
        hall p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
      rw [← pow_mul]
      obtain ⟨t, ht⟩ := he
      congr 1
      omega
    rw [hsq]
    by_cases h2 : 2 ∈ n.primeFactors
    · rw [← Finset.mul_prod_erase _ _ h2] at hprod
      exact hprod.symm
    · have hz : n.factorization 2 = 0 := by
        simpa [Nat.support_factorization] using
          (Nat.factorization n).notMem_support_iff.1 (by simpa [Nat.support_factorization] using h2)
      rw [hz, Finset.erase_eq_of_notMem h2, hprod, pow_zero, one_mul]

/-- **Parity structure of betrothed pairs.**  If the two members of a betrothed pair have the
same parity, then each of them is a power of two times a square (i.e. a square or twice a
square).  In particular a betrothed pair whose members are not of this shape must consist of
one even and one odd number, as is the case for all pairs known. -/
theorem IsBetrothedPair.two_pow_mul_sq_of_even_add {m n : ℕ} (h : IsBetrothedPair m n)
    (hpar : Even (m + n)) :
    (∃ a k : ℕ, 0 < k ∧ m = 2 ^ a * k ^ 2) ∧ (∃ a k : ℕ, 0 < k ∧ n = 2 ^ a * k ^ 2) := by
  obtain ⟨hm, hn, -, h1, h2⟩ := h
  have hodd : Odd (m + n + 1) := Even.add_one hpar
  exact ⟨eq_two_pow_mul_sq_of_odd_sigmaOne hm.ne' (h1 ▸ hodd),
    eq_two_pow_mul_sq_of_odd_sigmaOne hn.ne' (h2 ▸ hodd)⟩

/-- Contrapositive form: if one member of a betrothed pair is not a power of two times a
square, the two members have opposite parity. -/
theorem IsBetrothedPair.odd_add_of_not_two_pow_mul_sq {m n : ℕ} (h : IsBetrothedPair m n)
    (hm : ¬ ∃ a k : ℕ, 0 < k ∧ m = 2 ^ a * k ^ 2) : Odd (m + n) := by
  rcases Nat.even_or_odd (m + n) with he | ho
  · exact absurd (h.two_pow_mul_sq_of_even_add he).1 hm
  · exact ho

/-! ## The conditional infinitude statement -/

/-- **Betrothed Infinitude (conditional reduction).**

Whether infinitely many betrothed (quasi-amicable) pairs exist is an open problem, so the
statement is proved here as a reduction: the two-variable infinitude assertion follows from
the *one-variable* condition that arbitrarily large `m` satisfy `IsBetrothed m`, i.e.
`n := σ₁(m) - m - 1` is a positive number different from `m` with `σ₁(n) = σ₁(m)`. -/
theorem BetrothedInfinitude
    (H : ∀ N : ℕ, ∃ m, N < m ∧ IsBetrothed m) :
    {p : ℕ × ℕ | IsBetrothedPair p.1 p.2}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := (hfin.image Prod.fst).bddAbove
  obtain ⟨m, hmN, hm⟩ := H N
  obtain ⟨n, hn⟩ := (isBetrothed_iff m).1 hm
  have : m ∈ Prod.fst '' {p : ℕ × ℕ | IsBetrothedPair p.1 p.2} := ⟨(m, n), hn, rfl⟩
  exact absurd (hN this) (by omega)

/-- The hypothesis of `BetrothedInfinitude` is not merely sufficient but necessary: the
reduction is an equivalence. -/
theorem betrothedInfinitude_iff :
    {p : ℕ × ℕ | IsBetrothedPair p.1 p.2}.Infinite ↔ ∀ N : ℕ, ∃ m, N < m ∧ IsBetrothed m := by
  refine ⟨fun hinf N => ?_, BetrothedInfinitude⟩
  by_contra hc
  push_neg at hc
  have hsub : {p : ℕ × ℕ | IsBetrothedPair p.1 p.2} ⊆ Set.Iic N ×ˢ Set.Iic (N + N + 1) := by
    rintro ⟨m, n⟩ hmn
    have hm : IsBetrothed m := (isBetrothed_iff m).2 ⟨n, hmn⟩
    have hmN : m ≤ N := by by_contra h; exact absurd hm (hc m (by omega))
    have hn : IsBetrothed n := (isBetrothed_iff n).2 ⟨m, hmn.symm⟩
    have hnN : n ≤ N := by by_contra h; exact absurd hn (hc n (by omega))
    exact ⟨by simpa using hmN, by simp; omega⟩
  exact hinf (Set.Finite.subset ((Set.finite_Iic N).prod (Set.finite_Iic (N + N + 1))) hsub)

end Brockian.BetrothedNumbers

