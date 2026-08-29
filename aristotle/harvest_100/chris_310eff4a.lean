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

open Finset ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothed m n` says that `(m, n)` is a *betrothed* (quasi-amicable) pair:
two distinct positive integers each of whose sum of *proper* divisors is one more
than the other, i.e. `σ m = σ n = m + n + 1`. -/
def IsBetrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- `(48, 75)` is a betrothed pair; note that its two members have opposite parity. -/
theorem isBetrothed_48_75 : IsBetrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-! ### Parity of the sum of divisors -/

/-- The geometric sum `1 + p + ⋯ + p ^ k` for odd `p` is congruent to `k + 1` mod `2`. -/
theorem geomSum_mod_two_of_odd {p : ℕ} (hp : p % 2 = 1) (k : ℕ) :
    (∑ i ∈ range (k + 1), p ^ i) % 2 = (k + 1) % 2 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp, one_pow]
    omega

/-- The geometric sum `1 + 2 + ⋯ + 2 ^ k` is odd. -/
theorem geomSum_two_mod_two (k : ℕ) : (∑ i ∈ range (k + 1), 2 ^ i) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod]
    simp

/-- Parity of the geometric sum attached to a prime power. -/
theorem odd_geomSum_iff {p k : ℕ} (hp : p.Prime) :
    Odd (∑ i ∈ range (k + 1), p ^ i) ↔ (p = 2 ∨ Even k) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · simpa [Nat.odd_iff] using geomSum_two_mod_two k
  · have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    rw [Nat.odd_iff, geomSum_mod_two_of_odd hpo]
    simp only [hp2, false_or, Nat.even_iff]
    omega

/-- A positive natural number all of whose prime exponents are even is a square. -/
theorem exists_sq_of_even_factorization {m : ℕ} (hm : m ≠ 0)
    (h : ∀ p, Even (m.factorization p)) : ∃ t, m = t ^ 2 := by
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2), ?_⟩
  have hself : ∏ p ∈ m.primeFactors, p ^ m.factorization p = m := by
    have := Nat.factorization_prod_pow_eq_self hm
    rwa [Finsupp.prod, Nat.support_factorization] at this
  have key : ∏ p ∈ m.primeFactors, p ^ m.factorization p
      = (∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    obtain ⟨c, hc⟩ := h p
    rw [hc, ← pow_mul]
    congr 1
    omega
  exact hself.symm.trans key

/-- Being a square or twice a square is the same as having even exponent at every odd prime. -/
theorem sq_or_two_mul_sq_iff {n : ℕ} (hn : n ≠ 0) :
    (∃ a, n = a ^ 2 ∨ n = 2 * a ^ 2) ↔ ∀ p, p ≠ 2 → Even (n.factorization p) := by
  have h2p : ∀ p : ℕ, p ≠ 2 → (Nat.factorization 2) p = 0 := by
    intro p hp
    rw [Nat.Prime.factorization Nat.prime_two]
    simp [Ne.symm hp]
  constructor
  · rintro ⟨a, ha | ha⟩ p hp
    · subst ha
      rw [Nat.factorization_pow]
      exact ⟨a.factorization p, by simp [two_mul]⟩
    · have ha0 : a ≠ 0 := by rintro rfl; simp at ha; omega
      subst ha
      rw [Nat.factorization_mul (by norm_num) (pow_ne_zero 2 ha0), Nat.factorization_pow]
      simp only [Finsupp.add_apply, h2p p hp, zero_add, Finsupp.smul_apply, smul_eq_mul]
      exact ⟨a.factorization p, by ring⟩
  · intro h
    rcases Nat.even_or_odd (n.factorization 2) with he | ho
    · obtain ⟨t, ht⟩ := exists_sq_of_even_factorization hn (fun p => by
        rcases eq_or_ne p 2 with rfl | hp
        · exact he
        · exact h p hp)
      exact ⟨t, Or.inl ht⟩
    · have h2 : 2 ∣ n := by
        refine (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).mpr ?_
        rcases Nat.eq_zero_or_pos (n.factorization 2) with h0 | h0
        · rw [h0] at ho; simp at ho
        · exact h0
      obtain ⟨k, hk⟩ := h2
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hn hk
      have hfac : n.factorization = (Nat.factorization 2) + k.factorization := by
        rw [hk, Nat.factorization_mul (by norm_num) hk0]
      obtain ⟨t, ht⟩ := exists_sq_of_even_factorization hk0 (fun p => by
        rcases eq_or_ne p 2 with rfl | hp
        · have hval : n.factorization 2 = 1 + k.factorization 2 := by
            rw [hfac]
            simp [Nat.Prime.factorization Nat.prime_two]
          rw [Nat.odd_iff] at ho
          rw [Nat.even_iff]
          omega
        · have hnp : n.factorization p = k.factorization p := by
            rw [hfac]; simp [h2p p hp]
          rw [← hnp]
          exact h p hp)
      exact ⟨t, Or.inr (by rw [hk, ht])⟩

/-- **Parity of the sum of divisors**: `σ n` is odd exactly when `n` is a square
or twice a square. -/
theorem odd_sigma_iff {n : ℕ} (hn : n ≠ 0) :
    Odd (sigma 1 n) ↔ ∃ a, n = a ^ 2 ∨ n = 2 * a ^ 2 := by
  rw [sq_or_two_mul_sq_iff hn, sigma_one_apply, Nat.sum_divisors hn]
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd,
    Prime.dvd_finset_prod_iff Nat.prime_two.prime]
  constructor
  · intro h p hp
    by_cases hmem : p ∈ n.primeFactors
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
      by_contra hodd
      refine h ⟨p, hmem, ?_⟩
      have hns : ¬ Odd (∑ i ∈ range (n.factorization p + 1), p ^ i) := by
        rw [odd_geomSum_iff hpp]
        push_neg
        exact ⟨hp, hodd⟩
      rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hns
      exact hns
    · have hz : n.factorization p = 0 := by
        rw [← Nat.support_factorization] at hmem
        exact Finsupp.notMem_support_iff.mp hmem
      simp [hz]
  · rintro h ⟨p, hmem, hdvd⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
    have hodd : Odd (∑ i ∈ range (n.factorization p + 1), p ^ i) := by
      rw [odd_geomSum_iff hpp]
      rcases eq_or_ne p 2 with rfl | hp2
      · exact Or.inl rfl
      · exact Or.inr (h p hp2)
    rw [Nat.odd_iff] at hodd
    omega

/-! ### The reduction -/

/-- For a betrothed pair, having equal parity is equivalent to both members being
a square or twice a square. -/
theorem sameParity_iff_of_isBetrothed {m n : ℕ} (h : IsBetrothed m n) :
    m % 2 = n % 2 ↔
      ((∃ a, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧ (∃ b, n = b ^ 2 ∨ n = 2 * b ^ 2)) := by
  obtain ⟨hm, hn, -, hsm, hsn⟩ := h
  have hm0 : m ≠ 0 := hm.ne'
  have hn0 : n ≠ 0 := hn.ne'
  rw [← odd_sigma_iff hm0, ← odd_sigma_iff hn0, hsm, hsn, Nat.odd_iff]
  constructor
  · intro hpar
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, -⟩
    omega

/-- Being betrothed is a symmetric relation. -/
theorem isBetrothed_symm {m n : ℕ} (h : IsBetrothed m n) : IsBetrothed n m := by
  obtain ⟨hm, hn, hne, hsm, hsn⟩ := h
  exact ⟨hn, hm, hne.symm, by omega, by omega⟩

set_option maxRecDepth 100000 in
/-- An exhaustive check: for no `m < 1000` is `(m, σ m - m - 1)` a same-parity betrothed pair. -/
private theorem betrothed_check_below_1000 :
    ∀ m ∈ Finset.range 1000, ¬ (0 < m ∧ m ≠ sigma 1 m - m - 1 ∧
      sigma 1 (sigma 1 m - m - 1) = sigma 1 m ∧ m + (sigma 1 m - m - 1) + 1 = sigma 1 m ∧
      m % 2 = (sigma 1 m - m - 1) % 2) := by
  decide +kernel

/-- **Unconditional partial result**: both members of a same-parity betrothed pair,
if one exists, are at least `1000`. -/
theorem sameParity_betrothed_ge_1000 {m n : ℕ} (h : IsBetrothed m n) (hpar : m % 2 = n % 2) :
    1000 ≤ m ∧ 1000 ≤ n := by
  have main : ∀ a b : ℕ, IsBetrothed a b → a % 2 = b % 2 → 1000 ≤ a := by
    intro a b hb hp
    by_contra hlt
    push_neg at hlt
    obtain ⟨ha, hb0, hne, hsa, hsb⟩ := hb
    have hbv : b = sigma 1 a - a - 1 := by omega
    subst hbv
    exact betrothed_check_below_1000 a (Finset.mem_range.mpr hlt)
      ⟨ha, hne, by omega, by omega, hp⟩
  exact ⟨main m n h hpar, main n m (isBetrothed_symm h) hpar.symm⟩

/-- **Same-parity betrothed pairs, reduced.**

Whether a betrothed (quasi-amicable) pair of equal parity exists is an open problem.
This theorem gives a Lean-checked equivalent reformulation: such a pair exists if and
only if there is a betrothed pair both of whose members is a perfect square or twice
a perfect square.  (The underlying reason is `odd_sigma_iff`: for a betrothed pair the
common value `σ m = σ n = m + n + 1` is odd exactly when `m` and `n` have equal parity.)
See `sameParity_betrothed_ge_1000` for an unconditional partial result. -/
theorem SameParityBetrothedExists :
    (∃ m n : ℕ, IsBetrothed m n ∧ m % 2 = n % 2) ↔
      (∃ m n : ℕ, IsBetrothed m n ∧ (∃ a, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧
        (∃ b, n = b ^ 2 ∨ n = 2 * b ^ 2)) := by
  constructor
  · rintro ⟨m, n, hb, hpar⟩
    obtain ⟨h1, h2⟩ := (sameParity_iff_of_isBetrothed hb).mp hpar
    exact ⟨m, n, hb, h1, h2⟩
  · rintro ⟨m, n, hb, h1, h2⟩
    exact ⟨m, n, hb, (sameParity_iff_of_isBetrothed hb).mpr ⟨h1, h2⟩⟩

end Brockian.BetrothedNumbers

