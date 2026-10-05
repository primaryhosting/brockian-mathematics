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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` commands to precede every other command, including
module doc comments, so the header above is a plain comment and is repeated as the
module docstring after the import below.)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of all its divisors equals `2 * n + 1`,
i.e. `σ n = 2n + 1`.  Whether a quasiperfect number exists is an open problem. -/
def Quasiperfect (n : ℕ) : Prop :=
  0 < n ∧ ∑ d ∈ n.divisors, d = 2 * n + 1

/-- Every natural number `N` with `N % 4 = 3` has a prime factor `p` with `p % 4 = 3`. -/
theorem exists_prime_three_mod_four_dvd :
    ∀ N : ℕ, N % 4 = 3 → ∃ p, p.Prime ∧ p % 4 = 3 ∧ p ∣ N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    have hN1 : N ≠ 1 := by omega
    have hN0 : N ≠ 0 := by omega
    have hp : (N.minFac).Prime := Nat.minFac_prime hN1
    have hdvd : N.minFac ∣ N := Nat.minFac_dvd N
    obtain ⟨q, hq⟩ := hdvd
    have hodd : N % 2 = 1 := Nat.odd_of_mod_four_eq_three hN
    have hp2 : N.minFac % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exfalso
        have : (2 : ℕ) ∣ N := h ▸ Nat.minFac_dvd N
        omega
      · exact h
    have hpmod : N.minFac % 4 = 1 ∨ N.minFac % 4 = 3 := Nat.odd_mod_four_iff.mp hp2
    rcases hpmod with h1 | h3
    · -- minFac ≡ 1 mod 4, so the cofactor is ≡ 3 mod 4
      have hqmod : q % 4 = 3 := by
        have hmm : N % 4 = (N.minFac * q) % 4 := by rw [← hq]
        rw [Nat.mul_mod, h1, one_mul, Nat.mod_mod_of_dvd q (dvd_refl 4)] at hmm
        omega
      have hqlt : q < N := by
        have h2 : 2 ≤ N.minFac := hp.two_le
        have hq0 : 0 < q := by
          rcases Nat.eq_zero_or_pos q with rfl | h
          · simp at hq; omega
          · exact h
        calc q = 1 * q := (one_mul q).symm
          _ < N.minFac * q := Nat.mul_lt_mul_of_lt_of_le h2 le_rfl hq0
          _ = N := hq.symm
      obtain ⟨p, hp', hp3, hpd⟩ := ih q hqlt hqmod
      exact ⟨p, hp', hp3, hq ▸ hpd.mul_left _⟩
    · exact ⟨N.minFac, hp, h3, Nat.minFac_dvd N⟩

/-- No number congruent to `3` mod `4` divides a number of the form `k ^ 2 + 1`. -/
theorem not_dvd_sq_add_one_of_three_mod_four {D k : ℕ} (hD : D % 4 = 3) :
    ¬ D ∣ k ^ 2 + 1 := by
  intro hdvd
  obtain ⟨p, hp, hp3, hpd⟩ := exists_prime_three_mod_four_dvd D hD
  have hpk : p ∣ k ^ 2 + 1 := hpd.trans hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hz : ((k : ZMod p)) ^ 2 + 1 = 0 := by
    have h2 : ((k ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hpk
    push_cast at h2
    exact h2
  have hsq : IsSquare (-1 : ZMod p) := ⟨(k : ZMod p), by linear_combination -hz⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp3

/-- Every divisor of an odd number is odd. -/
theorem odd_of_dvd_odd {m d : ℕ} (hm : Odd m) (hd : d ∣ m) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso
    have : (2 : ℕ) ∣ m := (even_iff_two_dvd.mp he).trans hd
    rw [Nat.odd_iff] at hm
    omega
  · exact ho

/-- For odd `m`, the sum of divisors has the same parity as the number of divisors. -/
theorem sum_divisors_mod_two_of_odd {m : ℕ} (hm : Odd m) :
    (∑ d ∈ m.divisors, d) % 2 = (m.divisors.card) % 2 := by
  rw [Finset.sum_nat_mod]
  congr 1
  rw [Finset.sum_congr rfl (fun d hd => ?_), Finset.sum_const, smul_eq_mul, mul_one]
  have : Odd d := odd_of_dvd_odd hm (Nat.dvd_of_mem_divisors hd)
  exact Nat.odd_iff.mp this

/-- A positive number with an odd number of divisors is a perfect square. -/
theorem isSquare_of_odd_card_divisors {m : ℕ} (hm : m ≠ 0) (h : Odd m.divisors.card) :
    IsSquare m := by
  have hcard := Nat.card_divisors hm
  have heven : ∀ p ∈ m.primeFactors, Even (m.factorization p) := by
    intro p hp
    by_contra hodd
    have hoddp : m.factorization p % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd)
    have hdvd : (m.factorization p + 1) ∣ m.divisors.card := by
      rw [hcard]; exact Finset.dvd_prod_of_mem _ hp
    have h2 : (2 : ℕ) ∣ m.divisors.card :=
      dvd_trans ⟨(m.factorization p + 1) / 2, by omega⟩ hdvd
    have hc := Nat.odd_iff.mp h
    omega
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hm]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  obtain ⟨t, ht⟩ := heven p hp
  rw [ht, ← pow_add]
  congr 1
  omega

/-- If `m` is odd and `σ m` is odd, then `m` is a perfect square. -/
theorem isSquare_of_odd_sigma {m : ℕ} (hm0 : m ≠ 0) (hm : Odd m)
    (h : Odd (∑ d ∈ m.divisors, d)) : IsSquare m := by
  refine isSquare_of_odd_card_divisors hm0 ?_
  rw [Nat.odd_iff] at h ⊢
  rw [← sum_divisors_mod_two_of_odd hm]
  exact h

/-- The sum of divisors of `2 ^ a` is `2 ^ (a + 1) - 1`, stated without subtraction. -/
theorem sum_divisors_two_pow (a : ℕ) : (∑ d ∈ (2 ^ a).divisors, d) + 1 = 2 ^ (a + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    omega

/-- A quasiperfect number is an odd perfect square (necessarily bigger than 1). -/
theorem quasiperfect_eq_odd_sq {n : ℕ} (h : Quasiperfect n) :
    ∃ k, Odd k ∧ 1 < k ∧ n = k ^ 2 := by
  obtain ⟨hn0, hs⟩ := h
  -- first: `n` is odd
  have hodd : Odd n := by
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0.ne'
    by_contra hcon
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | hpos
      · exact absurd (by simpa using hm) hcon
      · exact hpos
    have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
    have hcop : (2 ^ a).Coprime m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
    have hsplit : ∑ d ∈ (2 ^ a * m).divisors, d
        = (∑ d ∈ (2 ^ a).divisors, d) * ∑ d ∈ m.divisors, d := Nat.Coprime.sum_divisors_mul hcop
    set D := ∑ d ∈ (2 ^ a).divisors, d with hDdef
    set S := ∑ d ∈ m.divisors, d with hSdef
    have hDS : D * S = 2 * (2 ^ a * m) + 1 := by rw [← hsplit]; exact hs
    have hD1 : D + 1 = 2 ^ (a + 1) := sum_divisors_two_pow a
    -- `S` is odd, hence `m` is a square
    have hSodd : Odd S := by
      rcases Nat.even_or_odd S with he | ho
      · exfalso
        obtain ⟨t, ht⟩ := he
        have : Even (D * S) := ⟨D * t, by rw [ht]; ring⟩
        rw [hDS] at this
        rcases this with ⟨u, hu⟩
        omega
      · exact ho
    obtain ⟨k, hk⟩ := isSquare_of_odd_sigma hm0 hm hSodd
    -- derive `D ∣ k ^ 2 + 1`
    have hk2 : m = k ^ 2 := by rw [hk]; ring
    have hpow : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    have hDS2 : D * S = D * k ^ 2 + (k ^ 2 + 1) := by
      have : 2 * (2 ^ a * m) = (D + 1) * k ^ 2 := by
        rw [hD1, hk2]; rw [hpow]; ring
      rw [hDS, this]; ring
    have hpow4 : 4 ≤ 2 ^ (a + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hD0 : 0 < D := by omega
    have hkS : k ^ 2 ≤ S := Nat.le_of_mul_le_mul_left (by omega) hD0
    have hdvd : D ∣ k ^ 2 + 1 := by
      refine ⟨S - k ^ 2, ?_⟩
      rw [Nat.mul_sub]
      omega
    have hD4 : D % 4 = 3 := by
      obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      subst hb
      have : 2 ^ (b + 1 + 1) = 4 * 2 ^ b := by ring
      have h2b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      omega
    exact not_dvd_sq_add_one_of_three_mod_four hD4 hdvd
  -- now: `n` odd with odd `σ n` gives a square
  have hSodd : Odd (∑ d ∈ n.divisors, d) := by rw [hs]; exact ⟨n, by ring⟩
  obtain ⟨k, hk⟩ := isSquare_of_odd_sigma hn0.ne' hodd hSodd
  have hk2 : n = k ^ 2 := by rw [hk]; ring
  refine ⟨k, ?_, ?_, hk2⟩
  · rcases Nat.even_or_odd k with he | ho
    · exfalso
      rw [Nat.odd_iff] at hodd
      obtain ⟨t, ht⟩ := he
      rw [hk2, ht] at hodd
      have : (2 * t) ^ 2 % 2 = 0 := by
        have : (2 * t) ^ 2 = 2 * (2 * t * t) := by ring
        omega
      rw [show t + t = 2 * t by ring] at hodd
      omega
    · exact ho
  · by_contra hcon
    have hk1 : k = 1 ∨ k = 0 := by omega
    rcases hk1 with rfl | rfl
    · rw [hk2] at hs; norm_num at hs
    · rw [hk2] at hn0; norm_num at hn0

/-- A quasiperfect number is odd. -/
theorem Quasiperfect.odd {n : ℕ} (h : Quasiperfect n) : Odd n := by
  obtain ⟨k, hk, _, rfl⟩ := quasiperfect_eq_odd_sq h
  exact hk.pow

/-- A quasiperfect number is a perfect square. -/
theorem Quasiperfect.isSquare {n : ℕ} (h : Quasiperfect n) : IsSquare n := by
  obtain ⟨k, _, _, rfl⟩ := quasiperfect_eq_odd_sq h
  exact ⟨k, by ring⟩

set_option maxRecDepth 10000 in
/-- A finite check: there is no quasiperfect number below `200`. -/
theorem not_quasiperfect_of_lt_two_hundred {n : ℕ} (hn : n < 200) : ¬ Quasiperfect n := by
  have h : ∀ m < 200, ¬ (0 < m ∧ ∑ d ∈ m.divisors, d = 2 * m + 1) := by decide
  exact h n hn

/-- **Conditional reduction for the existence of quasiperfect numbers.**

If a quasiperfect number exists at all, then one exists which is the square of an odd
number greater than `1`.  (Whether a quasiperfect number exists is an open problem.) -/
theorem QuasiperfectExists :
    (∃ n, Quasiperfect n) → ∃ k, Odd k ∧ 1 < k ∧ Quasiperfect (k ^ 2) := by
  rintro ⟨n, hn⟩
  obtain ⟨k, hk, hk1, rfl⟩ := quasiperfect_eq_odd_sq hn
  exact ⟨k, hk, hk1, hn⟩

end QuasiperfectNumbers
end Brockian

