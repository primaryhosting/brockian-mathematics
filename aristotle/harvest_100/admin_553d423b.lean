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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- A *betrothed* (quasi-amicable) pair: two distinct positive numbers each of whose
sum of divisors equals `m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- The smallest betrothed pair, `(48, 75)`; note the two members have opposite parity. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

theorem betrothed_symm {m n : ℕ} (h : Betrothed m n) : Betrothed n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  exact ⟨hn, hm, hne.symm, by omega, by omega⟩

/-! ### Parity of the sum-of-divisors function -/

private lemma odd_prod_iff (s : Finset ℕ) (f : ℕ → ℕ) :
    Odd (∏ p ∈ s, f p) ↔ ∀ p ∈ s, Odd (f p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, Nat.odd_mul, ih, forall_and, or_imp]

private lemma odd_geom_sum_odd {p a : ℕ} (hp : Odd p) :
    Odd (∑ i ∈ Finset.range (a + 1), p ^ i) ↔ Even a := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hpow : Odd (p ^ (n + 1)) := hp.pow
    simp only [Nat.odd_iff, Nat.even_iff] at *
    omega

private lemma odd_geom_sum_two (a : ℕ) : Odd (∑ i ∈ Finset.range (a + 1), 2 ^ i) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact ih.add_even (by simp [Nat.even_pow])

/-- `σ n` is odd exactly when every odd prime occurs to an even power in `n`. -/
theorem odd_sigma_one_iff_factorization {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p) := by
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [mul_one, odd_prod_iff]
  refine ⟨fun h p hp hp2 => ?_, fun h p hp => ?_⟩
  · have hodd : Odd p := (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two hp2
    exact (odd_geom_sum_odd hodd).1 (h p hp)
  · rcases eq_or_ne p 2 with rfl | hp2
    · exact odd_geom_sum_two _
    · exact (odd_geom_sum_odd ((Nat.prime_of_mem_primeFactors hp).odd_of_ne_two hp2)).2 (h p hp hp2)

/-- Having all odd primes to even powers means being `2 ^ a` times a square. -/
theorem factorization_even_iff_two_pow_mul_sq {n : ℕ} (hn : n ≠ 0) :
    (∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p)) ↔ ∃ a k, n = 2 ^ a * k ^ 2 := by
  constructor
  · intro h
    obtain ⟨s, b, hab, hsf⟩ := Nat.sq_mul_squarefree n
    have hb0 : b ≠ 0 := by rintro rfl; simp at hab; omega
    have hs0 : s ≠ 0 := hsf.ne_zero
    have hfac : ∀ p, n.factorization p = 2 * b.factorization p + s.factorization p := by
      intro p
      rw [← hab, Nat.factorization_mul (by positivity) hs0]
      simp [Nat.factorization_pow, two_mul]
    have key : ∀ p, p.Prime → p ∣ s → p = 2 := by
      intro p hp hps
      by_contra hne
      have hpn : p ∣ n := hab ▸ hps.mul_left _
      have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, hn⟩
      have h1 : s.factorization p = 1 := by
        have hle := Squarefree.natFactorization_le_one p hsf
        have hge := hp.factorization_pos_of_dvd hs0 hps
        omega
      have hev := h p hmem hne
      rw [hfac, h1] at hev
      simp [parity_simps] at hev
    have hs2 : s = 1 ∨ s = 2 := by
      have h4 : ¬ (4 ∣ s) := by
        intro h4
        have := hsf 2 (by omega : (2 : ℕ) * 2 ∣ s)
        simp at this
      rcases eq_or_ne s 1 with h1 | h1
      · exact Or.inl h1
      · obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd h1
        have hp2 := key p hp hps
        subst hp2
        right
        obtain ⟨t, rfl⟩ := hps
        have ht : ¬ (2 ∣ t) := by
          rintro ⟨u, rfl⟩; exact h4 ⟨u, by ring⟩
        have ht1 : t = 1 := by
          by_contra htne
          obtain ⟨q, hq, hqt⟩ := Nat.exists_prime_and_dvd htne
          exact ht ((key q hq (hqt.mul_left 2)) ▸ hqt)
        simp [ht1]
    rcases hs2 with rfl | rfl
    · exact ⟨0, b, by simpa using hab.symm⟩
    · exact ⟨1, b, by rw [← hab]; ring⟩
  · rintro ⟨a, k, rfl⟩ p hp hp2
    have hk0 : k ≠ 0 := by rintro rfl; simp at hn
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h2 : ((2 : ℕ) ^ a).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hd))
    have h3 : (2 ^ a * k ^ 2).factorization p = 2 * k.factorization p := by
      rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hk0),
        Finsupp.add_apply, h2, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, zero_add]
    rw [h3]
    exact even_two_mul _

/-- `σ n` is odd exactly when `n` is a square or twice a square. -/
theorem odd_sigma_one_iff {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ (IsSquare n ∨ ∃ k, n = 2 * k ^ 2) := by
  rw [odd_sigma_one_iff_factorization hn, factorization_even_iff_two_pow_mul_sq hn]
  constructor
  · rintro ⟨a, k, rfl⟩
    rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      exact ⟨2 ^ b * k, by subst hb; ring⟩
    · right
      exact ⟨2 ^ b * k, by subst hb; ring⟩
  · rintro (⟨r, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨0, r, by ring⟩
    · exact ⟨1, k, by ring⟩

/-! ### Parity of betrothed pairs -/

/-- For a betrothed pair, the two members have the same parity iff `σ m` is odd. -/
theorem sameParity_iff_odd_sigma {m n : ℕ} (h : Betrothed m n) :
    m % 2 = n % 2 ↔ Odd (σ 1 m) := by
  obtain ⟨-, -, -, h1, -⟩ := h
  rw [h1, Nat.odd_iff]
  omega

/-- Any member of a same-parity betrothed pair is a square or twice a square. -/
theorem sameParity_betrothed_isSquare_or_two_mul_sq {m n : ℕ} (h : Betrothed m n)
    (hpar : m % 2 = n % 2) : (IsSquare m ∨ ∃ k, m = 2 * k ^ 2) := by
  have hm : m ≠ 0 := h.1.ne'
  exact (odd_sigma_one_iff hm).1 ((sameParity_iff_odd_sigma h).1 hpar)

/-- Both members of a same-parity betrothed pair are squares or twice squares. -/
theorem sameParity_betrothed_structure {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    (IsSquare m ∨ ∃ k, m = 2 * k ^ 2) ∧ (IsSquare n ∨ ∃ k, n = 2 * k ^ 2) :=
  ⟨sameParity_betrothed_isSquare_or_two_mul_sq h hpar,
    sameParity_betrothed_isSquare_or_two_mul_sq (betrothed_symm h) hpar.symm⟩

/-- A betrothed pair of two odd numbers would consist of two perfect squares. -/
theorem betrothed_odd_isSquare {m n : ℕ} (h : Betrothed m n) (hm : Odd m) (hn : Odd n) :
    IsSquare m ∧ IsSquare n := by
  have hpar : m % 2 = n % 2 := by
    rw [Nat.odd_iff] at hm hn; omega
  obtain ⟨h1, h2⟩ := sameParity_betrothed_structure h hpar
  constructor
  · rcases h1 with h1 | ⟨k, rfl⟩
    · exact h1
    · exact absurd hm (by simp [Nat.odd_iff, Nat.mul_mod_right])
  · rcases h2 with h2 | ⟨k, rfl⟩
    · exact h2
    · exact absurd hn (by simp [Nat.odd_iff, Nat.mul_mod_right])

/-- **Reduction for the existence of a same-parity betrothed pair.**

Whether a betrothed (quasi-amicable) pair whose two members have the same parity exists is an
open problem: all known betrothed pairs consist of one even and one odd number.  The theorem
below is a Lean-checked *reduction*: such a pair exists if and only if there is a betrothed
pair one of whose members is a square or twice a square.  (The two directions come from the
fact that `σ k` is odd exactly for `k` a square or twice a square, together with
`σ m = m + n + 1` for a betrothed pair.) -/
theorem SameParityBetrothedExists :
    (∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2) ↔
      (∃ m n : ℕ, Betrothed m n ∧ (IsSquare m ∨ ∃ k, m = 2 * k ^ 2)) := by
  constructor
  · rintro ⟨m, n, h, hpar⟩
    exact ⟨m, n, h, sameParity_betrothed_isSquare_or_two_mul_sq h hpar⟩
  · rintro ⟨m, n, h, hm⟩
    refine ⟨m, n, h, ?_⟩
    exact (sameParity_iff_odd_sigma h).2 ((odd_sigma_one_iff h.1.ne').2 hm)

end BetrothedNumbers

end Brockian

