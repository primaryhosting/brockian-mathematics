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
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

set_option autoImplicit false

namespace Brockian.QuasiperfectNumbers

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of its divisors
equals `2 * n + 1` (equivalently, the sum of its proper divisors is `n + 1`).
No quasiperfect number is known, and their existence is an open problem. -/
def Quasiperfect (n : ℕ) : Prop := 0 < n ∧ σ 1 n = 2 * n + 1

/-- Restatement of quasiperfection in terms of the sum of divisors. -/
theorem quasiperfect_iff_sum_divisors {n : ℕ} :
    Quasiperfect n ↔ 0 < n ∧ ∑ d ∈ n.divisors, d = 2 * n + 1 := by
  simp [Quasiperfect, sigma_one_apply]

/-! ### Auxiliary arithmetic lemmas -/

/-- If `D ≡ 3 [MOD 4]` then `D` divides no number of the form `m ^ 2 + 1`;
i.e. `-1` is not a square modulo such a `D`. -/
theorem not_dvd_sq_add_one_of_three_mod_four {D m : ℕ} (hD : D % 4 = 3)
    (hdvd : D ∣ m ^ 2 + 1) : False := by
  have hDodd : Odd D := by rw [Nat.odd_iff]; omega
  have hcop : Int.gcd (m : ℤ) (D : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    by_contra hg
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
    have h1 : p ∣ m ^ 2 := dvd_pow (hpd.trans (Nat.gcd_dvd_left _ _)) two_ne_zero
    have h2 : p ∣ m ^ 2 + 1 := (hpd.trans (Nat.gcd_dvd_right _ _)).trans hdvd
    have h3 : p ∣ 1 := (Nat.dvd_add_right h1).mp h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  have h1 : jacobiSym ((m : ℤ) ^ 2) D = 1 := jacobiSym.sq_one' hcop
  have hmod : ((m : ℤ) ^ 2) % (D : ℤ) = (-1) % (D : ℤ) := by
    have hz : (D : ℤ) ∣ (m : ℤ) ^ 2 + 1 := by exact_mod_cast Int.natCast_dvd_natCast.2 hdvd
    exact (Int.modEq_iff_dvd.2 (by simpa using hz)).symm
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hDodd,
    ZMod.χ₄_nat_three_mod_four hD] at h1
  norm_num at h1

/-- A nonzero natural number all of whose prime exponents are even is a square. -/
theorem isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := h p
  omega

/-- A number with an odd number of divisors is a square. -/
theorem isSquare_of_odd_card_divisors {n : ℕ} (hn : n ≠ 0) (h : Odd n.divisors.card) :
    IsSquare n := by
  refine isSquare_of_factorization_even hn (fun p => ?_)
  by_cases hp : p ∈ n.primeFactors
  · by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hdvd : (n.factorization p + 1) ∣ n.divisors.card := by
      rw [Nat.card_divisors hn]; exact Finset.dvd_prod_of_mem _ hp
    have h2 : 2 ∣ (n.factorization p + 1) := by obtain ⟨k, hk⟩ := hodd; omega
    have h3 : 2 ∣ n.divisors.card := h2.trans hdvd
    rw [Nat.odd_iff] at h
    omega
  · have : n.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hp
    simp [this]

/-- For an odd number `n`, the sum of divisors has the same parity as the number of divisors. -/
theorem sigma_one_mod_two_of_odd {n : ℕ} (hn : Odd n) :
    (σ 1 n) % 2 = n.divisors.card % 2 := by
  rw [sigma_one_apply]
  have hdvd_odd : ∀ d ∈ n.divisors, Odd d := by
    intro d hd
    exact hn.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
  have hcast : ((∑ d ∈ n.divisors, d : ℕ) : ZMod 2) = (n.divisors.card : ZMod 2) := by
    push_cast
    rw [Finset.sum_congr rfl (fun d hd => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
    obtain ⟨k, hk⟩ := hdvd_odd d hd
    subst hk; push_cast; ring_nf; simp [show (2 : ZMod 2) = 0 by decide]
  simpa using (ZMod.natCast_eq_natCast_iff' _ _ 2).1 hcast

/-- An odd number whose sum of divisors is odd is a square. -/
theorem isSquare_of_odd_of_odd_sigma {n : ℕ} (hn : Odd n) (h : Odd (σ 1 n)) : IsSquare n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine isSquare_of_odd_card_divisors hn0 ?_
  rw [Nat.odd_iff] at h ⊢
  rw [← sigma_one_mod_two_of_odd hn, h]

/-- `σ 1 (2 ^ a) + 1 = 2 ^ (a + 1)`. -/
theorem sigma_two_pow_add_one (a : ℕ) : σ 1 (2 ^ a) + 1 = 2 ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ k ih =>
    have h : σ 1 (2 ^ (k + 1)) = σ 1 (2 ^ k) + 2 ^ (k + 1) := by
      rw [sigma_one_apply, sigma_one_apply,
        Nat.sum_divisors_prime_pow Nat.prime_two (f := fun x => x),
        Nat.sum_divisors_prime_pow Nat.prime_two (f := fun x => x),
        Finset.sum_range_succ]
    rw [h]
    ring_nf
    ring_nf at ih
    omega

/-! ### Cattaneo's theorem: a quasiperfect number is an odd square -/

/-- Every quasiperfect number is odd. -/
theorem Quasiperfect.odd {n : ℕ} (h : Quasiperfect n) : Odd n := by
  obtain ⟨hpos, hsig⟩ := h
  rw [Nat.odd_iff]
  by_contra hev
  have hn0 : n ≠ 0 := hpos.ne'
  obtain ⟨a, q, hq, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  -- `a ≥ 1` since `n` is even
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · simp only [pow_zero, one_mul] at hev
      rw [Nat.odd_iff] at hq; omega
    · exact h
  have hcop : Nat.Coprime (2 ^ a) q := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hq)
  have hmul : σ 1 (2 ^ a * q) = σ 1 (2 ^ a) * σ 1 q :=
    isMultiplicative_sigma.map_mul_of_coprime hcop
  set S := σ 1 (2 ^ a) with hS
  have hSq : S + 1 = 2 ^ (a + 1) := sigma_two_pow_add_one a
  -- the main equation
  have key : S * σ 1 q = S * q + (q + 1) := by
    rw [← hmul, hsig]
    have : 2 * (2 ^ a * q) = (S + 1) * q := by rw [hSq]; ring
    omega
  have hSdvd : S ∣ q + 1 := by
    refine (Nat.dvd_add_right (Dvd.intro (σ 1 q) rfl)).mp ?_
    exact ⟨σ 1 q, by omega⟩
  -- `q` is a square
  have hsigq_odd : Odd (σ 1 q) := by
    rcases Nat.even_or_odd (σ 1 q) with he | ho
    · exfalso
      obtain ⟨k, hk⟩ := he
      have : Odd (σ 1 (2 ^ a * q)) := by rw [hsig]; exact ⟨2 ^ a * q, by ring⟩
      rw [hmul, hk] at this
      rw [Nat.odd_iff] at this
      omega
    · exact ho
  obtain ⟨m, hm⟩ := isSquare_of_odd_of_odd_sigma hq hsigq_odd
  -- `S ≡ 3 [MOD 4]`
  have hS4 : S % 4 = 3 := by
    have h4 : (4 : ℕ) ∣ 2 ^ (a + 1) := by
      have : (2 : ℕ) ^ 2 ∣ 2 ^ (a + 1) := pow_dvd_pow 2 (by omega)
      simpa using this
    obtain ⟨c, hc⟩ := h4
    omega
  refine not_dvd_sq_add_one_of_three_mod_four (m := m) hS4 ?_
  rw [← hm] at hSdvd ⊢
  rwa [pow_two]

/-- Every quasiperfect number is a perfect square (Cattaneo). -/
theorem Quasiperfect.isSquare {n : ℕ} (h : Quasiperfect n) : IsSquare n := by
  refine isSquare_of_odd_of_odd_sigma h.odd ?_
  rw [h.2]
  exact ⟨n, by ring⟩

/-! ### The reduction -/

/-- **Quasiperfect numbers exist iff an odd square quasiperfect number exists.**

The existence of a quasiperfect number (a number `n` with `σ n = 2 n + 1`) is a famous open
problem, so we record here a Lean-checked equivalent reformulation: a quasiperfect number
exists if and only if there is an *odd* number `m` whose *square* is quasiperfect.
The nontrivial direction is Cattaneo's theorem, proved above: any quasiperfect number is
necessarily an odd perfect square. -/
theorem QuasiperfectExists :
    (∃ n : ℕ, Quasiperfect n) ↔ (∃ m : ℕ, Odd m ∧ Quasiperfect (m ^ 2)) := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := hn.isSquare
    have hn' : n = m ^ 2 := by rw [hm, pow_two]
    refine ⟨m, ?_, hn' ▸ hn⟩
    have hodd := hn.odd
    rw [hn', pow_two, Nat.odd_mul] at hodd
    exact hodd.1
  · rintro ⟨m, _, hm⟩
    exact ⟨m ^ 2, hm⟩

end Brockian.QuasiperfectNumbers

