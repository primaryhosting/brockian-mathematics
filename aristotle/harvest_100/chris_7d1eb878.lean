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

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- `Betrothed m n` says that `m` and `n` are a pair of *betrothed*
(quasi-amicable) numbers: two distinct positive integers each of whose sum of
divisors equals `m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧
    (∑ d ∈ m.divisors, d) = m + n + 1 ∧ (∑ d ∈ n.divisors, d) = m + n + 1

/-- The smallest betrothed pair, `(48, 75)`; note the two members have
opposite parity. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- Auxiliary: a natural number all of whose prime exponents are even is a
square. -/
theorem isSquare_of_even_factorization {m : ℕ} (hm : m ≠ 0)
    (h : ∀ p, Even (m.factorization p)) : ∃ k, m = k ^ 2 := by
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2), ?_⟩
  rw [← Finset.prod_pow]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hm]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_mul]
  congr 1
  obtain ⟨c, hc⟩ := h p
  omega

/-- Auxiliary: for odd `p`, the geometric sum `1 + p + ⋯ + p ^ (N-1)` is
congruent to `N` modulo `2`. -/
theorem geom_sum_mod_two {p : ℕ} (hp : Odd p) (N : ℕ) :
    (∑ k ∈ Finset.range N, p ^ k) % 2 = N % 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hpk : p ^ N % 2 = 1 := Nat.odd_iff.mp (hp.pow)
      omega

/-- Key classical fact: if the sum of divisors of `n` is odd, then `n` is
either a square or twice a square. -/
theorem exists_sq_of_odd_sigma {n : ℕ} (hn : n ≠ 0)
    (h : Odd (∑ d ∈ n.divisors, d)) : ∃ k, n = k ^ 2 ∨ n = 2 * k ^ 2 := by
  -- every odd prime occurs to an even power
  have key : ∀ p : ℕ, p.Prime → p ≠ 2 → Even (n.factorization p) := by
    intro p hp hp2
    by_contra hodd
    have hmem : p ∈ n.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, hn⟩
      by_contra hdvd
      exact hodd (by simp [Nat.factorization_eq_zero_of_not_dvd hdvd])
    have hdvd : (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) ∣
        ∏ q ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization q + 1), q ^ k :=
      Finset.dvd_prod_of_mem _ hmem
    rw [← Nat.sum_divisors hn] at hdvd
    have heven : 2 ∣ (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) := by
      have h1 := geom_sum_mod_two (p := p) (hp.odd_of_ne_two hp2) (n.factorization p + 1)
      have h2 : (n.factorization p + 1) % 2 = 0 := by
        rcases Nat.even_or_odd (n.factorization p) with he | ho
        · exact absurd he hodd
        · rw [Nat.odd_iff] at ho; omega
      omega
    have hdvd2 : 2 ∣ ∑ d ∈ n.divisors, d := heven.trans hdvd
    rw [Nat.odd_iff] at h
    omega
  set a := n.factorization 2 with ha
  set m := n / 2 ^ a with hmdef
  have hmn : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos 2 hn).ne'
  have hmfac : ∀ p, Even (m.factorization p) := by
    intro p
    rw [hmdef, ha, Nat.factorization_ordCompl]
    by_cases hp2 : p = 2
    · simp [hp2]
    · rw [Finsupp.erase_ne hp2]
      by_cases hp : p.Prime
      · exact key p hp hp2
      · simp [Nat.factorization_eq_zero_of_not_prime n hp]
  obtain ⟨k, hk⟩ := isSquare_of_even_factorization hm0 hmfac
  rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  · refine ⟨2 ^ b * k, Or.inl ?_⟩
    rw [← hmn, hk, hb]
    ring
  · refine ⟨2 ^ b * k, Or.inr ?_⟩
    rw [← hmn, hk, hb]
    ring

/-- Necessary condition: in a betrothed pair whose members have the same
parity, each member is a perfect square or twice a perfect square.  (For such a
pair the common divisor sum `m + n + 1` is odd.) -/
theorem sq_or_two_sq_of_betrothed_sameParity {m n : ℕ} (hB : Betrothed m n)
    (hpar : m % 2 = n % 2) :
    (∃ a, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧ (∃ b, n = b ^ 2 ∨ n = 2 * b ^ 2) := by
  obtain ⟨hm, hn, _, hsm, hsn⟩ := hB
  have hoddm : Odd (∑ d ∈ m.divisors, d) := by rw [hsm, Nat.odd_iff]; omega
  have hoddn : Odd (∑ d ∈ n.divisors, d) := by rw [hsn, Nat.odd_iff]; omega
  exact ⟨exists_sq_of_odd_sigma hm.ne' hoddm, exists_sq_of_odd_sigma hn.ne' hoddn⟩

/-- **Conditional reduction for the Brockian "same parity betrothed" problem.**

It is a longstanding open question whether there exists a betrothed
(quasi-amicable) pair whose two members have the same parity; all known pairs
consist of one even and one odd number.

We prove the following unconditional structural reduction: *if* a same-parity
betrothed pair exists, then such a pair exists in which each member is either a
perfect square or twice a perfect square.  Indeed, for a same-parity pair the
common value `m + n + 1` of the two divisor sums is odd, and a number has odd
divisor sum exactly when it is a square or twice a square. -/
theorem SameParityBetrothedExists :
    (∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2) →
    (∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2 ∧
      (∃ a, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧ (∃ b, n = b ^ 2 ∨ n = 2 * b ^ 2)) := by
  rintro ⟨m, n, hB, hpar⟩
  obtain ⟨h1, h2⟩ := sq_or_two_sq_of_betrothed_sameParity hB hpar
  exact ⟨m, n, hB, hpar, h1, h2⟩

end BetrothedNumbers
end Brockian

