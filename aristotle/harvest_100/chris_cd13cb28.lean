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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Betrothed (quasi-amicable) numbers

A pair `(m, n)` of distinct positive integers is *betrothed* (or *quasi-amicable*,
or a *reduced amicable pair*) when

  `σ m = σ n = m + n + 1`,

i.e. each of `m` and `n` is the sum of the *nontrivial* proper divisors of the other.
The smallest example is `(48, 75)`.

Whether there are infinitely many betrothed pairs is an open problem, so the target
theorem `BetrothedInfinitude` is stated here as a **Lean-checked conditional
reduction**: infinitude of betrothed pairs follows from a prime-pattern hypothesis
`PrimePatternUnbounded`, which asks for arbitrarily large solutions of a pair of
`σ`-equations in which the two "new" factors are primes.

The hypothesis is *not* vacuous: `isBetrothedPattern_16_25_3_3` exhibits the
solution `(a, b, p, q) = (16, 25, 3, 3)`, which produces the betrothed pair
`(48, 75)`.

Alongside the reduction, several unconditional facts are proved: the first three
betrothed pairs, that no member of a betrothed pair is prime, that both members are
at least `48`, that the set of betrothed pairs is infinite exactly when betrothed
numbers are unbounded, and a parity restriction (in a betrothed pair whose two members
have the same parity, each member is a square or twice a square).
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

set_option maxRecDepth 100000

/-- `IsBetrothedPair m n` says that `m` and `n` are distinct positive integers with
`σ m = σ n = m + n + 1`; equivalently, each is the sum of the proper divisors of the
other, excluding `1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- The set of betrothed pairs, as a subset of `ℕ × ℕ`. -/
def BetrothedPairs : Set (ℕ × ℕ) := {p | IsBetrothedPair p.1 p.2}

/-- A number is *betrothed* if it belongs to some betrothed pair. -/
def IsBetrothed (m : ℕ) : Prop := ∃ n, IsBetrothedPair m n

theorem isBetrothedPair_comm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hmn, h1, h2⟩ := h
  refine ⟨hn, hm, hmn.symm, ?_, ?_⟩ <;> omega

/-! ### Small examples -/

theorem isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

theorem isBetrothedPair_140_195 : IsBetrothedPair 140 195 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

theorem isBetrothedPair_1050_1925 : IsBetrothedPair 1050 1925 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-! ### Unconditional restrictions on betrothed pairs -/

/-- No member of a betrothed pair is prime: a prime `p` has `σ p = p + 1`, which would
force the partner to be `0`. -/
theorem not_prime_of_isBetrothedPair {m n : ℕ} (h : IsBetrothedPair m n) : ¬ m.Prime := by
  intro hp
  obtain ⟨-, hn, -, h1, -⟩ := h
  rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors] at h1
  omega

/-- Both members of a betrothed pair are at least `48`; the pair `(48, 75)` is the
smallest one. -/
theorem forty_eight_le_of_isBetrothedPair {m n : ℕ} (h : IsBetrothedPair m n) : 48 ≤ m := by
  obtain ⟨hm, hn, hmn, h1, h2⟩ := h
  by_contra hlt
  push_neg at hlt
  have hbound : ∀ k < 48, sigma 1 k ≤ 96 := by decide
  have hn' : n < 100 := by have := hbound m hlt; omega
  have key : ∀ a < 48, ∀ b < 100, ¬ (0 < a ∧ 0 < b ∧ a ≠ b ∧
      sigma 1 a = a + b + 1 ∧ sigma 1 b = a + b + 1) := by decide
  exact key m hlt n hn' ⟨hm, hn, hmn, h1, h2⟩

/-! #### Parity of `σ` and a restriction on same-parity betrothed pairs -/

/-- For an odd prime `p`, `σ (p ^ k)` is odd exactly when `k` is even. -/
theorem odd_sigma_prime_pow_iff {p k : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) :
    Odd (sigma 1 (p ^ k)) ↔ Even k := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  have h1 : ∀ i ∈ Finset.range (k + 1), p ^ i % 2 = 1 := by
    intro i _
    rw [Nat.pow_mod, hodd, one_pow, Nat.one_mod_eq_one.mpr (by norm_num)]
  rw [Nat.odd_iff, Finset.sum_nat_mod, Finset.sum_congr rfl h1]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, Nat.even_iff]
  omega

/-- `σ (2 ^ k)` is always odd. -/
theorem odd_sigma_two_pow (k : ℕ) : Odd (sigma 1 (2 ^ k)) := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact ih.add_even ⟨2 ^ n, by ring⟩

/-- A positive integer with odd `σ`-value is a square or twice a square. -/
theorem sq_or_two_mul_sq_of_odd_sigma :
    ∀ m : ℕ, 0 < m → Odd (sigma 1 m) → ∃ k, m = k ^ 2 ∨ m = 2 * k ^ 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hodd
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm.ne') with h1 | h1
    · exact ⟨1, Or.inl (by omega)⟩
    · set p := m.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hdvd : p ∣ m := Nat.minFac_dvd m
      set e := m.factorization p with hedef
      set c := m / p ^ e with hcdef
      have hsplit : p ^ e * c = m := Nat.ordProj_mul_ordCompl_eq_self m p
      have hcpos : 0 < c := Nat.ordCompl_pos p hm.ne'
      have hcop : Nat.Coprime (p ^ e) c :=
        Nat.Coprime.pow_left e (Nat.coprime_ordCompl hp hm.ne')
      have he1 : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd hp hm.ne' hdvd
      have hclt : c < m := by
        have hpe : 2 ≤ p ^ e := by
          calc 2 ≤ p := hp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
        nlinarith
      have hsig : sigma 1 m = sigma 1 (p ^ e) * sigma 1 c := by
        rw [← hsplit]
        exact isMultiplicative_sigma.map_mul_of_coprime hcop
      rw [hsig, Nat.odd_mul] at hodd
      obtain ⟨hodd1, hodd2⟩ := hodd
      obtain ⟨k, hk⟩ := ih c hclt hcpos hodd2
      rcases Nat.Prime.eq_two_or_odd hp with hp2 | hpodd
      · have hcodd : ¬ p ∣ c := Nat.not_dvd_ordCompl hp hm.ne'
        rw [hp2] at hcodd
        have hkc : c = k ^ 2 := by
          rcases hk with h | h
          · exact h
          · exact absurd ⟨k ^ 2, h⟩ hcodd
        rcases Nat.even_or_odd e with ⟨t, ht⟩ | ⟨t, ht⟩
        · exact ⟨2 ^ t * k, Or.inl (by rw [← hsplit, hp2, hkc, ht]; ring)⟩
        · exact ⟨2 ^ t * k, Or.inr (by rw [← hsplit, hp2, hkc, ht]; ring)⟩
      · obtain ⟨t, ht⟩ := (odd_sigma_prime_pow_iff hp hpodd).mp hodd1
        rcases hk with h | h
        · exact ⟨p ^ t * k, Or.inl (by rw [← hsplit, h, ht]; ring)⟩
        · exact ⟨p ^ t * k, Or.inr (by rw [← hsplit, h, ht]; ring)⟩

/-- If the two members of a betrothed pair have the same parity, then their common
`σ`-value is odd. -/
theorem odd_sigma_of_same_parity {m n : ℕ} (h : IsBetrothedPair m n) (hpar : m % 2 = n % 2) :
    Odd (sigma 1 m) ∧ Odd (sigma 1 n) := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  constructor <;> [rw [h1]; rw [h2]] <;> exact ⟨(m + n) / 2, by omega⟩

/-- **Parity restriction.** In a betrothed pair whose two members have the same parity,
each member is a square or twice a square. (All known betrothed pairs consist of one
even and one odd member, so this rules out same-parity pairs except in a very thin
family.) -/
theorem sq_or_two_mul_sq_of_same_parity {m n : ℕ} (h : IsBetrothedPair m n)
    (hpar : m % 2 = n % 2) :
    (∃ k, m = k ^ 2 ∨ m = 2 * k ^ 2) ∧ (∃ k, n = k ^ 2 ∨ n = 2 * k ^ 2) := by
  obtain ⟨hm, hn, -, -, -⟩ := id h
  obtain ⟨hom, hon⟩ := odd_sigma_of_same_parity h hpar
  exact ⟨sq_or_two_mul_sq_of_odd_sigma m hm hom, sq_or_two_mul_sq_of_odd_sigma n hn hon⟩

/-- The partner of a betrothed number is unique: it is `σ m - m - 1`. -/
theorem partner_unique {m n n' : ℕ} (h : IsBetrothedPair m n) (h' : IsBetrothedPair m n') :
    n = n' := by
  obtain ⟨-, -, -, h1, -⟩ := h
  obtain ⟨-, -, -, h2, -⟩ := h'
  omega

/-- The betrothed pairs form an infinite set exactly when betrothed numbers are
unbounded. -/
theorem betrothedPairs_infinite_iff :
    BetrothedPairs.Infinite ↔ ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothedPair m n := by
  constructor
  · intro hinf N
    by_contra hcon
    push_neg at hcon
    have hsub : Prod.fst '' BetrothedPairs ⊆ Set.Iic N := by
      rintro x ⟨⟨m, n⟩, hmem, rfl⟩
      exact Nat.not_lt.mp fun hlt => (hcon m n hlt) hmem
    have hinj : Set.InjOn Prod.fst BetrothedPairs := by
      rintro ⟨m, n⟩ hmn ⟨m', n'⟩ hmn' (heq : m = m')
      subst heq
      exact Prod.ext rfl (partner_unique hmn hmn')
    exact hinf (((Set.finite_Iic N).subset hsub).of_finite_image hinj)
  · intro H
    refine Set.Infinite.of_image Prod.fst (Set.infinite_of_not_bddAbove ?_)
    rintro ⟨B, hB⟩
    obtain ⟨m, n, hlt, hpair⟩ := H B
    exact absurd (hB ⟨(m, n), hpair, rfl⟩) (by omega)

/-! ### A prime-pattern reduction -/

/-- The prime pattern underlying the reduction: `a, b` are positive, `p, q` are primes
not dividing `a, b` respectively, and the two `σ`-equations defining a betrothed pair
hold for `m = a * p`, `n = b * q` after using multiplicativity of `σ`. -/
def IsBetrothedPattern (a b p q : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ p.Prime ∧ q.Prime ∧ ¬ p ∣ a ∧ ¬ q ∣ b ∧ a * p ≠ b * q ∧
    sigma 1 a * (p + 1) = sigma 1 b * (q + 1) ∧
    sigma 1 a * (p + 1) = a * p + b * q + 1

/-- The hypothesis of the reduction: arbitrarily large solutions of the prime pattern. -/
def PrimePatternUnbounded : Prop :=
  ∀ N : ℕ, ∃ a b p q : ℕ, N < a * p ∧ IsBetrothedPattern a b p q

/-- The pattern is non-vacuous: `(a, b, p, q) = (16, 25, 3, 3)` is a solution,
producing the betrothed pair `(48, 75)`. -/
theorem isBetrothedPattern_16_25_3_3 : IsBetrothedPattern 16 25 3 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, by decide,
    by norm_num, ?_, ?_⟩ <;> decide

/-- A solution of the prime pattern yields a betrothed pair. -/
theorem isBetrothedPair_of_pattern {a b p q : ℕ} (h : IsBetrothedPattern a b p q) :
    IsBetrothedPair (a * p) (b * q) := by
  obtain ⟨ha, hb, hp, hq, hpa, hqb, hne, heq, hsum⟩ := h
  have hcop : Nat.Coprime a p := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpa |>.symm
  have hcoq : Nat.Coprime b q := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqb |>.symm
  have hsa : sigma 1 (a * p) = sigma 1 a * (p + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_one_apply p,
      hp.sum_divisors]
  have hsb : sigma 1 (b * q) = sigma 1 b * (q + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcoq, ArithmeticFunction.sigma_one_apply q,
      hq.sum_divisors]
  refine ⟨Nat.mul_pos ha hp.pos, Nat.mul_pos hb hq.pos, hne, ?_, ?_⟩
  · rw [hsa]; exact hsum
  · rw [hsb, ← heq]; exact hsum

/-- **Betrothed Infinitude (conditional reduction).**

If the prime pattern `IsBetrothedPattern` has arbitrarily large solutions, then there
are infinitely many betrothed (quasi-amicable) pairs.

Unconditional infinitude of betrothed pairs is an open problem; this theorem reduces it
to the prime-pattern hypothesis `PrimePatternUnbounded`, which is known to have at least
one solution (`isBetrothedPattern_16_25_3_3`, giving the pair `(48, 75)`). -/
theorem BetrothedInfinitude (H : PrimePatternUnbounded) : BetrothedPairs.Infinite := by
  rw [betrothedPairs_infinite_iff]
  intro N
  obtain ⟨a, b, p, q, hlt, hpat⟩ := H N
  exact ⟨a * p, b * q, hlt, isBetrothedPair_of_pattern hpat⟩

/-- Consequently, under the same hypothesis there are infinitely many betrothed numbers. -/
theorem infinite_setOf_isBetrothed (H : PrimePatternUnbounded) :
    {m : ℕ | IsBetrothed m}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨a, b, p, q, hlt, hpat⟩ := H B
  have hmem : a * p ∈ {m : ℕ | IsBetrothed m} := ⟨b * q, isBetrothedPair_of_pattern hpat⟩
  exact absurd (hB hmem) (by omega)

end BetrothedNumbers
end Brockian

