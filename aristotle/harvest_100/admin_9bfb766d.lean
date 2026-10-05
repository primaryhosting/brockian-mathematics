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

(Note: Lean 4 does not allow a module doc comment before `import`, so the required
header appears here as an ordinary comment and is repeated as the module docstring below.)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Summary

A *quasiperfect* number is a natural number `n` with `σ(n) = 2n + 1`, i.e. the sum of the
proper divisors of `n` equals `n + 1`.  No quasiperfect number is known and their existence
is an open problem.  We prove here the classical structural constraints: any quasiperfect
number is an odd perfect square greater than `1`, and package this as a Lean-checked
reduction `QuasiperfectExists` of the existence question.
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A natural number `n` is *quasiperfect* if `σ(n) = 2n + 1`, i.e. the sum of the proper
divisors of `n` is `n + 1`.  No quasiperfect number is known, and it is an open problem
whether one exists. -/
def Quasiperfect (n : ℕ) : Prop := 0 < n ∧ sigmaOne n = 2 * n + 1

/-- For odd `n`, the sum of divisors has the same parity as the number of divisors. -/
lemma sigmaOne_mod_two_of_odd {n : ℕ} (hn : Odd n) :
    sigmaOne n % 2 = n.divisors.card % 2 := by
  have h : ∀ d ∈ n.divisors, d % 2 = 1 := by
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hn' : n % 2 = 1 := Nat.odd_iff.mp hn
    have h2 : ¬ (2 ∣ d) := by
      intro h2
      have := h2.trans hdvd
      omega
    omega
  unfold sigmaOne
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl h]
  simp

/-- A positive number with an odd number of divisors is a square. -/
lemma isSquare_of_odd_card_divisors {n : ℕ} (hn : n ≠ 0) (h : Odd n.divisors.card) :
    IsSquare n := by
  have hev : ∀ p, Even (n.factorization p) := by
    intro p
    by_cases hp : p ∈ n.primeFactors
    · by_contra hodd
      rw [Nat.card_divisors hn] at h
      have hdvd : (n.factorization p + 1) ∣ ∏ q ∈ n.primeFactors, (n.factorization q + 1) :=
        Finset.dvd_prod_of_mem _ hp
      have h2 : 2 ∣ (n.factorization p + 1) := by
        rcases Nat.even_or_odd (n.factorization p) with he | ho
        · exact absurd he hodd
        · have := Nat.odd_iff.mp ho; omega
      have := h2.trans hdvd
      have := Nat.odd_iff.mp h
      omega
    · have hz : n.factorization p = 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.notMem_support_iff.mp hp
      simp [hz]
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  have ha1 : a = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd hne
    have hpn : n.factorization p = 2 * b.factorization p + a.factorization p := by
      rw [← hab, Nat.factorization_mul (by positivity) (by omega)]
      simp [Nat.factorization_pow, two_mul]
    have hfa : a.factorization p = 1 := by
      have h1 := (Nat.squarefree_iff_factorization_le_one (by omega)).mp hsq p
      have hpos : 1 ≤ a.factorization p := hp.factorization_pos_of_dvd (by omega) hpa
      omega
    have hE := hev p
    rw [hpn, hfa] at hE
    rcases hE with ⟨c, hc⟩
    omega
  subst ha1
  exact ⟨b, by rw [← hab]; ring⟩

/-- An odd number with an odd sum of divisors is a square. -/
lemma isSquare_of_odd_sigmaOne {n : ℕ} (hn : Odd n) (h : Odd (sigmaOne n)) : IsSquare n := by
  refine isSquare_of_odd_card_divisors (by rintro rfl; simp at hn) ?_
  rw [Nat.odd_iff, ← sigmaOne_mod_two_of_odd hn, ← Nat.odd_iff]
  exact h

/-- `σ(2 ^ a) = 2 ^ (a + 1) - 1`, stated without truncated subtraction. -/
lemma sigmaOne_two_pow (a : ℕ) : sigmaOne (2 ^ a) + 1 = 2 ^ (a + 1) := by
  unfold sigmaOne
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction a with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; omega

/-- A product of natural numbers all congruent to `1` mod `4` is congruent to `1` mod `4`. -/
lemma list_prod_mod_four {l : List ℕ} (h : ∀ x ∈ l, x % 4 = 1) : l.prod % 4 = 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.prod_cons, Nat.mul_mod, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- If every prime factor of `m` is `≡ 1 (mod 4)` then `m ≡ 1 (mod 4)`. -/
lemma mod_four_eq_one_of_primeFactors {m : ℕ} (hm : m ≠ 0)
    (h : ∀ q ∈ m.primeFactors, q % 4 = 1) : m % 4 = 1 := by
  rw [← Nat.prod_primeFactorsList hm]
  refine list_prod_mod_four (fun x hx => h x ?_)
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactorsList hx,
    Nat.dvd_of_mem_primeFactorsList hx, hm⟩

/-- A number `m ≡ 3 (mod 4)` never divides `v ^ 2 + 1`: otherwise `-1` would be a square
modulo `m`, whereas `m` must have a prime factor `≡ 3 (mod 4)`. -/
lemma not_dvd_sq_add_one_of_mod_four_eq_three {m v : ℕ} (hm : m % 4 = 3) :
    ¬ m ∣ v ^ 2 + 1 := by
  intro hdvd
  have hm0 : m ≠ 0 := by omega
  haveI : NeZero m := ⟨hm0⟩
  have hsq : IsSquare (-1 : ZMod m) := by
    refine ⟨(v : ZMod m), ?_⟩
    have h0 : ((v ^ 2 + 1 : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    linear_combination -h0
  have hall : ∀ q ∈ m.primeFactors, q % 4 = 1 := by
    intro q hq
    have h3 := Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hq hsq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    rcases hqp.eq_two_or_odd with h2 | h2
    · subst h2; omega
    · omega
  have := mod_four_eq_one_of_primeFactors hm0 hall
  omega

/-- **Every quasiperfect number is odd.**

If `n = 2 ^ k * u` with `u` odd and `k ≥ 1`, then `σ(n) = (2 ^ (k+1) - 1) * σ(u) = 2n + 1`
forces `M := 2 ^ (k+1) - 1` to divide `u + 1`, while `σ(u)` is odd, so `u = v ^ 2`.
Thus `M ≡ 3 (mod 4)` divides `v ^ 2 + 1`, which is impossible. -/
theorem quasiperfect_odd {n : ℕ} (h : Quasiperfect n) : Odd n := by
  obtain ⟨hpos, heq⟩ := h
  rw [Nat.odd_iff]
  by_contra hev
  have hn0 : n ≠ 0 := by omega
  obtain ⟨k, u, huodd, hfac⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hk1 : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [pow_zero, one_mul] at hfac
    exact hev (by rw [hfac]; exact Nat.odd_iff.mp huodd)
  have hcop : Nat.Coprime (2 ^ k) u :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr huodd)
  have hmul : sigmaOne n = sigmaOne (2 ^ k) * sigmaOne u := by
    rw [hfac]; exact hcop.sum_divisors_mul
  set S := sigmaOne (2 ^ k) with hS
  have hSpow : S + 1 = 2 ^ (k + 1) := sigmaOne_two_pow k
  have key : S * sigmaOne u = S * u + (u + 1) := by
    have h1 : S * sigmaOne u = 2 * (2 ^ k * u) + 1 := by rw [← hmul, ← hfac]; exact heq
    have h2 : 2 * (2 ^ k * u) = S * u + u := by
      rw [show (2 : ℕ) * (2 ^ k * u) = 2 ^ (k + 1) * u by ring, ← hSpow]; ring
    omega
  have hSu : sigmaOne u ≥ u := by
    by_contra hlt
    have h3 : S * sigmaOne u ≤ S * u := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨t, ht⟩ : ∃ t, sigmaOne u = u + t := ⟨sigmaOne u - u, by omega⟩
  have hSt : S * t = u + 1 := by
    rw [ht, Nat.mul_add] at key; omega
  have hS4 : S % 4 = 3 := by
    have h4 : (4 : ℕ) ∣ 2 ^ (k + 1) := by
      refine ⟨2 ^ (k - 1), ?_⟩
      rw [show k + 1 = 2 + (k - 1) by omega, pow_add]; norm_num
    omega
  have hsigu : Odd (sigmaOne u) := by
    rw [Nat.odd_iff]
    by_contra hce
    have hdvd : 2 ∣ sigmaOne u := by omega
    have hdvd2 : 2 ∣ S * sigmaOne u := hdvd.mul_left S
    have h1 : S * sigmaOne u = 2 * n + 1 := by rw [← hmul]; exact heq
    omega
  obtain ⟨v, hv⟩ := isSquare_of_odd_sigmaOne huodd hsigu
  refine not_dvd_sq_add_one_of_mod_four_eq_three (v := v) hS4 ⟨t, ?_⟩
  rw [hv] at hSt
  rw [hSt]; ring

/-- Every quasiperfect number is a perfect square. -/
theorem quasiperfect_isSquare {n : ℕ} (h : Quasiperfect n) : IsSquare n :=
  isSquare_of_odd_sigmaOne (quasiperfect_odd h) (by rw [h.2]; exact ⟨n, by ring⟩)

/-- Every quasiperfect number exceeds `1`. -/
theorem quasiperfect_one_lt {n : ℕ} (h : Quasiperfect n) : 1 < n := by
  obtain ⟨hpos, heq⟩ := h
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · exact h1
  · have hn1 : n = 1 := by omega
    subst hn1
    simp [sigmaOne] at heq

/-- For `p ≥ 3` the geometric sum `1 + p + ⋯ + p ^ k` is smaller than `2 * p ^ k`. -/
lemma sum_geom_lt_two_mul {p : ℕ} (hp : 3 ≤ p) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), p ^ i < 2 * p ^ k := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have h1 : 2 * p ^ m ≤ p ^ (m + 1) := by
        rw [pow_succ, mul_comm (p ^ m) p, mul_comm 2 (p ^ m), mul_comm p (p ^ m)]
        exact Nat.mul_le_mul_left _ (by omega)
      omega

/-- No quasiperfect number is a prime power: for an odd prime `p` one has
`σ(p ^ k) < 2 * p ^ k`. -/
theorem quasiperfect_not_isPrimePow {n : ℕ} (h : Quasiperfect n) : ¬ IsPrimePow n := by
  rintro ⟨p, k, hp, hk, hpk⟩
  have hodd : Odd n := quasiperfect_odd h
  have hpn : Nat.Prime p := Nat.prime_iff.mpr hp
  have hp3 : 3 ≤ p := by
    rcases hpn.eq_two_or_odd' with rfl | hpo
    · exfalso
      have h2 : (2 : ℕ) ∣ n := hpk ▸ dvd_pow_self 2 (by omega)
      have := Nat.odd_iff.mp hodd
      omega
    · have := hpn.two_le
      have := Nat.odd_iff.mp hpo
      omega
  obtain ⟨-, heq⟩ := h
  subst hpk
  rw [sigmaOne, Nat.sum_divisors_prime_pow hpn] at heq
  have := sum_geom_lt_two_mul hp3 k
  omega

/-- **Conditional reduction for the existence of quasiperfect numbers.**

Whether a quasiperfect number (a number `n` with `σ(n) = 2n + 1`) exists is an open problem.
This theorem reduces the search: a quasiperfect number exists if and only if there is an
odd perfect square `n > 1`, not a prime power, with `σ(n) = 2n + 1`. -/
theorem QuasiperfectExists :
    (∃ n : ℕ, Quasiperfect n) ↔
      ∃ n : ℕ, 1 < n ∧ Odd n ∧ IsSquare n ∧ ¬ IsPrimePow n ∧ sigmaOne n = 2 * n + 1 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, quasiperfect_one_lt hn, quasiperfect_odd hn, quasiperfect_isSquare hn,
      quasiperfect_not_isPrimePow hn, hn.2⟩
  · rintro ⟨n, hn1, -, -, -, hn⟩
    exact ⟨n, by omega, hn⟩

end QuasiperfectNumbers
end Brockian

