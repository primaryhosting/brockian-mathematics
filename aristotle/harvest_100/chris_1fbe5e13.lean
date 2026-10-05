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

-- (The header above uses `/-` rather than `/-!` only because Lean 4 does not allow a module
-- docstring to precede the `import` commands.)

import Mathlib

open Nat ArithmeticFunction

namespace Brockian
namespace BetrothedNumbers

/-- Two positive naturals `m`, `n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the *proper* divisors of each,
excluding `1`, gives the other number. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ (∑ d ∈ m.divisors, d) = m + n + 1 ∧ (∑ d ∈ n.divisors, d) = m + n + 1

/-- `(48, 75)` is a betrothed pair, so the notion is not vacuous.  Note the two members have
opposite parity, as in every known example. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- If the sum of divisors of `n` is odd, then every odd prime occurs to an even power in `n`. -/
theorem even_factorization_of_odd_sigma {n : ℕ} (hn : n ≠ 0)
    (hodd : Odd (∑ d ∈ n.divisors, d)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Even (n.factorization p) := by
  by_cases hpn : p ∈ n.primeFactors
  · rw [← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn] at hodd
    set a := n.factorization p with ha
    have hdvd : (∑ i ∈ Finset.range (a + 1), p ^ (i * 1)) ∣
        ∏ q ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization q + 1), q ^ (i * 1) :=
      Finset.dvd_prod_of_mem _ hpn
    have hS : Odd (∑ i ∈ Finset.range (a + 1), p ^ (i * 1)) := by
      rcases Nat.even_or_odd (∑ i ∈ Finset.range (a + 1), p ^ (i * 1)) with he | ho
      · exact absurd (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp he) hdvd))
          (Nat.not_even_iff_odd.mpr hodd)
      · exact ho
    have hmod : (∑ i ∈ Finset.range (a + 1), p ^ (i * 1)) % 2 = (a + 1) % 2 := by
      rw [Finset.sum_nat_mod]
      have hone : ∀ i ∈ Finset.range (a + 1), p ^ (i * 1) % 2 = 1 := by
        intro i _
        exact Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
      rw [Finset.sum_congr rfl hone]
      simp
    rw [Nat.odd_iff, hmod] at hS
    rw [Nat.even_iff]
    omega
  · have hnd : ¬ p ∣ n := fun hd => hpn (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]
    exact even_zero

/-- A squarefree number all of whose prime factors equal `2` is either `1` or `2`. -/
theorem eq_one_or_two_of_squarefree {a : ℕ} (hsq : Squarefree a)
    (h : ∀ p : ℕ, p.Prime → p ∣ a → p = 2) : a = 1 ∨ a = 2 := by
  have ha0 : a ≠ 0 := hsq.ne_zero
  rcases eq_or_ne a 1 with rfl | h1
  · exact Or.inl rfl
  · obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd h1
    have hp2 : p = 2 := h p hp hpa
    subst hp2
    have hle : a.factorization 2 ≤ 1 := by
      by_contra hc
      have h4 : (2 : ℕ) ^ 2 ∣ a :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ha0).mpr (by omega)
      exact Nat.prime_two.not_isUnit (hsq 2 (by simpa [pow_two] using h4))
    have hge : 1 ≤ a.factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ha0).mp (by simpa using hpa)
    have heq : a = 2 ^ a.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd ha0 (fun {d} hd hda => h d hd hda)
    -- the exponent is exactly `a.factorization 2`
    have hlen : a.primeFactorsList.length = a.factorization 2 := by
      conv_rhs => rw [heq]
      simp [Nat.prime_two.factorization]
    rw [hlen] at heq
    right
    rw [heq]
    have : a.factorization 2 = 1 := le_antisymm hle hge
    rw [this, pow_one]

/-- A positive number all of whose odd primes occur to an even power is a square or twice a
square. -/
theorem eq_sq_or_two_mul_sq_of_even_odd_factorization {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → Even (n.factorization p)) :
    ∃ k : ℕ, n = k ^ 2 ∨ n = 2 * k ^ 2 := by
  obtain ⟨a, b, hab, hsq⟩ := Nat.sq_mul_squarefree n
  have ha0 : a ≠ 0 := hsq.ne_zero
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hab
    exact hn hab.symm
  have key : ∀ p : ℕ, p.Prime → p ∣ a → p = 2 := by
    intro p hp hpa
    by_contra hp2
    have hfa : a.factorization p = 1 := by
      have hle : a.factorization p ≤ 1 := by
        by_contra hc
        have hpp : p ^ 2 ∣ a :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp ha0).mpr (by omega)
        exact hp.not_isUnit (hsq p (by simpa [pow_two] using hpp))
      have hge : 1 ≤ a.factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp ha0).mp (by simpa using hpa)
      omega
    have hfn : n.factorization p = 2 * b.factorization p + 1 := by
      rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0]
      simp [Nat.factorization_pow, hfa]
    have := h p hp hp2
    rw [hfn, Nat.even_iff] at this
    omega
  rcases eq_one_or_two_of_squarefree hsq key with rfl | rfl
  · exact ⟨b, Or.inl (by rw [← hab]; ring)⟩
  · exact ⟨b, Or.inr (by rw [← hab]; ring)⟩

/-- If a betrothed pair has both members of the same parity, then each member is either a perfect
square or twice a perfect square. -/
theorem sq_or_two_mul_sq_of_betrothed_same_parity {m n : ℕ} (h : Betrothed m n)
    (hpar : m % 2 = n % 2) :
    (∃ a : ℕ, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧ (∃ b : ℕ, n = b ^ 2 ∨ n = 2 * b ^ 2) := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  have hodd : Odd (m + n + 1) := by
    rw [Nat.odd_iff]
    omega
  constructor
  · refine eq_sq_or_two_mul_sq_of_even_odd_factorization hm.ne' ?_
    intro p hp hp2
    exact even_factorization_of_odd_sigma hm.ne' (hsm ▸ hodd) hp hp2
  · refine eq_sq_or_two_mul_sq_of_even_odd_factorization hn.ne' ?_
    intro p hp hp2
    exact even_factorization_of_odd_sigma hn.ne' (hsn ▸ hodd) hp hp2

/-- **Same parity betrothed numbers.**  Whether a betrothed (quasi-amicable) pair of equal parity
exists is an open problem; all known betrothed pairs consist of one even and one odd number.  Here
we give a Lean-checked conditional reduction: *if* such a pair exists, then it may be taken with
both members of the very restricted shape `k ^ 2` or `2 * k ^ 2` (a consequence of the fact that
the common divisor sum `m + n + 1` is then odd). -/
theorem SameParityBetrothedExists
    (hex : ∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2) :
    ∃ m n a b : ℕ, Betrothed m n ∧ m % 2 = n % 2 ∧
      (m = a ^ 2 ∨ m = 2 * a ^ 2) ∧ (n = b ^ 2 ∨ n = 2 * b ^ 2) := by
  obtain ⟨m, n, hmn, hpar⟩ := hex
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := sq_or_two_mul_sq_of_betrothed_same_parity hmn hpar
  exact ⟨m, n, a, b, hmn, hpar, ha, hb⟩

end BetrothedNumbers
end Brockian

