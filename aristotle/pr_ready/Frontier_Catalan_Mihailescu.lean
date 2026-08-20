/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Statement: 8 and 9 are the only consecutive perfect powers (x^p − y^q = 1 ⇒ 3²−2³).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

Catalan's conjecture, proved by Mihailescu (2004), states that the only pair of consecutive
perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`; equivalently the only solution of
`x ^ p - y ^ q = 1` in integers `x, y, p, q > 1` is `3 ^ 2 - 2 ^ 3 = 1`.

Mihailescu's theorem is **not** available in Mathlib (a search of Mathlib turns up no
`Catalan`/`Mihailescu` result about the exponential Diophantine equation; the files mentioning
"Catalan" concern Catalan *numbers*, and `Mathlib/NumberTheory/FLT/Polynomial.lean` only contains
the *polynomial* analogue).  Accordingly this file:

* formalizes the statement (`Frontier.IsCatalanPair`);
* proves *unconditionally* the elementary base cases:
  - equal exponents (`Frontier.not_isCatalanPair_of_eq_exponents`),
  - base `2` on the left (`Frontier.not_isCatalanPair_two_left`): `2 ^ p` is never one more
    than a perfect power,
  - base `2` on the right (`Frontier.isCatalanPair_two_right`): the only perfect power that
    is one more than a power of two is `9 = 2 ^ 3 + 1`;
* proves a Lean-checked **reduction** (`Frontier.Catalan_Mihailescu`) of the full statement,
  for arbitrary exponents `> 1`, to the genuinely deep *core case* `Frontier.CatalanCoreCase`:
  distinct **prime** exponents and both bases `≥ 3`.
-/

namespace Frontier

/-- `IsCatalanPair x p y q` says that `x ^ p - y ^ q = 1`, where all four of
`x, y, p, q` are `> 1`; i.e. `x ^ p` and `y ^ q` are consecutive perfect powers. -/
def IsCatalanPair (x p y q : ℕ) : Prop :=
  1 < x ∧ 1 < p ∧ 1 < y ∧ 1 < q ∧ x ^ p = y ^ q + 1

/-- `8 = 2 ^ 3` and `9 = 3 ^ 2` are consecutive perfect powers. -/
theorem isCatalanPair_three_two_two_three : IsCatalanPair 3 2 2 3 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### Elementary tools -/

/-- An odd natural number dividing a power of two is `1`. -/
theorem eq_one_of_odd_of_dvd_two_pow {d n : ℕ} (hd : Odd d) (h : d ∣ 2 ^ n) : d = 1 := by
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 h with ⟨k, hk, rfl⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exact absurd hd (by simp [Nat.odd_pow_iff, hk0.ne'])

/-- If `1 < x` and `x ^ k = c` with `1 < c < 4`, then `k = 1` and `x = c`. -/
theorem exponent_eq_one_of_pow_lt_four {x k c : ℕ} (hx : 1 < x) (hc : 1 < c) (hc4 : c < 4)
    (h : x ^ k = c) : k = 1 ∧ x = c := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simpa using h
  · exfalso
    have h1 : 2 ^ (k + 1 + 1) ≤ x ^ (k + 1 + 1) := Nat.pow_le_pow_left hx _
    have h2 : (4 : ℕ) ≤ 2 ^ (k + 1 + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- If `x ≥ 3` is odd, `p` is odd and `x ^ p - 1` is a power of two, then `p = 1`.
The point is that `(x ^ p - 1) / (x - 1) = ∑ i < p, x ^ i` is odd, hence equal to `1`. -/
theorem odd_pow_sub_one_two_pow {x p n : ℕ} (hx3 : 3 ≤ x) (hxo : Odd x) (hp : Odd p)
    (h : x ^ p = 2 ^ n + 1) : p = 1 := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 := ⟨x - 1, by omega⟩
  set S : ℕ := ∑ i ∈ Finset.range p, (z + 1) ^ i with hS
  have hnat : (z + 1) ^ p = z * S + 1 := by
    have h2 := geom_sum_mul ((z : ℤ) + 1) p
    have h3 : ((z : ℤ) + 1) ^ p = (z : ℤ) * (∑ i ∈ Finset.range p, ((z : ℤ) + 1) ^ i) + 1 := by
      ring_nf at h2 ⊢
      linarith
    have h4 : ((z + 1 : ℕ) ^ p : ℤ) = ((z * S + 1 : ℕ) : ℤ) := by
      push_cast [hS]
      convert h3 using 2
    exact_mod_cast h4
  have hdvd : S ∣ 2 ^ n := ⟨z, by rw [mul_comm]; omega⟩
  have hSodd : Odd S := by
    rw [Nat.odd_iff, hS, Finset.sum_nat_mod]
    have hterm : ∀ i ∈ Finset.range p, (z + 1) ^ i % 2 = 1 := fun i _ => Nat.odd_iff.1 hxo.pow
    rw [Finset.sum_congr rfl hterm]
    simp [Nat.odd_iff.1 hp]
  have hS1 : S = 1 := eq_one_of_odd_of_dvd_two_pow hSodd hdvd
  have hpow : (z + 1) ^ p = (z + 1) ^ 1 := by rw [hS1] at hnat; simpa using hnat
  exact Nat.pow_right_injective (by omega) hpow

/-- If `y ≥ 3` is odd, `q` is odd and `y ^ q + 1` is a power of two, then `q = 1`.
The point is that `(y ^ q + 1) / (y + 1) = ∑ i < q, (-1) ^ i y ^ i` is odd, hence equal to `1`. -/
theorem odd_pow_add_one_two_pow {y q n : ℕ} (hy3 : 3 ≤ y) (hyo : Odd y) (hq : Odd q)
    (h : y ^ q + 1 = 2 ^ n) : q = 1 := by
  have hcast : ((2 : ℤ) ^ n) = ((y : ℕ) ^ q + 1 : ℕ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h.symm
  set T : ℤ := ∑ i ∈ Finset.range q, (y : ℤ) ^ i * (-1) ^ (q - 1 - i) with hT
  have hmul : T * ((y : ℤ) + 1) = 2 ^ n := by
    have h2 := geom_sum₂_mul ((y : ℤ)) (-1) q
    rw [hq.neg_one_pow] at h2
    rw [show ((y : ℤ) - (-1)) = (y : ℤ) + 1 by ring] at h2
    rw [hT, h2]
    push_cast at hcast
    linarith
  have hTodd : Odd T := by
    rw [Int.odd_iff, hT, Finset.sum_int_mod]
    have hterm : ∀ i ∈ Finset.range q, ((y : ℤ) ^ i * (-1) ^ (q - 1 - i)) % 2 = 1 := by
      intro i _
      exact Int.odd_iff.1 (Odd.mul ((Int.odd_coe_nat y).2 hyo).pow (Odd.pow (by decide)))
    rw [Finset.sum_congr rfl hterm]
    simp [Int.odd_iff.1 (by exact_mod_cast hq : Odd (q : ℤ))]
  have hTpos : 0 < T := by
    rcases lt_trichotomy T 0 with hlt | heq | hgt
    · nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) n]
    · rw [heq] at hmul; simp at hmul; nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) n]
    · exact hgt
  have hdvd : T.natAbs ∣ 2 ^ n := by
    have h1 : T ∣ (2 : ℤ) ^ n := ⟨(y : ℤ) + 1, hmul.symm⟩
    simpa using Int.natAbs_dvd_natAbs.2 h1
  have hT1 : T = 1 := by
    have := eq_one_of_odd_of_dvd_two_pow (Int.natAbs_odd.2 hTodd) hdvd
    omega
  rw [hT1, one_mul] at hmul
  have hpow : (y : ℤ) ^ q = (y : ℤ) ^ 1 := by
    push_cast at hcast
    simp
    linarith
  exact Nat.pow_right_injective (show 2 ≤ y by omega) (by exact_mod_cast hpow : y ^ q = y ^ 1)

/-! ### Base cases of Catalan's equation -/

/-- **Equal exponents**: `x ^ n - y ^ n = 1` has no solution with `x, y, n > 1`. -/
theorem not_isCatalanPair_of_eq_exponents (x y n : ℕ) : ¬ IsCatalanPair x n y n := by
  rintro ⟨-, hn, hy, -, h⟩
  have hxy : y + 1 ≤ x := by
    by_contra hc
    push_neg at hc
    have : x ^ n ≤ y ^ n := Nat.pow_le_pow_left (by omega) _
    omega
  have key : ∀ m : ℕ, 2 ≤ m → y ^ m + 2 ≤ (y + 1) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => ring_nf; nlinarith
    | succ m hm ih =>
        have hrw : (y + 1) ^ (m + 1) = (y + 1) * (y + 1) ^ m := by ring
        have hp : y ^ (m + 1) = y * y ^ m := by ring
        have h2 : (y + 1) * (y ^ m + 2) ≤ (y + 1) * (y + 1) ^ m := Nat.mul_le_mul_left _ ih
        rw [hrw, hp]
        nlinarith [pow_pos (show 0 < y by omega) m]
  have k1 := key n hn
  have k2 : (y + 1) ^ n ≤ x ^ n := Nat.pow_le_pow_left hxy _
  omega

/-- **Base `2` on the left**: `2 ^ p - y ^ q = 1` has no solution with `y, p, q > 1`.
(A power of two is never one more than a perfect power.) -/
theorem not_isCatalanPair_two_left (p y q : ℕ) : ¬ IsCatalanPair 2 p y q := by
  rintro ⟨-, hp, hy, hq, h⟩
  have h2p : (2 : ℕ) ^ p % 2 = 0 := by
    have : (2 : ℕ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hyo : Odd y := by
    rw [Nat.odd_iff]
    by_contra hc
    have hey : Even y := Nat.even_iff.2 (by omega)
    have : Even (y ^ q) := Nat.even_pow.2 ⟨hey, by omega⟩
    rw [Nat.even_iff] at this
    omega
  have hy3 : 3 ≤ y := by rcases hyo with ⟨m, hm⟩; omega
  rcases Nat.even_or_odd q with ⟨k, hk⟩ | hqo
  · -- `q` even: `(y ^ k) ^ 2 + 1 ≡ 2 [MOD 4]`, but `4 ∣ 2 ^ p`.
    have hz : (y ^ k) ^ 2 + 1 = 2 ^ p := by
      rw [← pow_mul, show k * 2 = q by omega]; omega
    obtain ⟨m, hm⟩ : Odd (y ^ k) := hyo.pow
    have h4 : 2 ^ p = 4 * 2 ^ (p - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1; omega
    have hexp : (y ^ k) ^ 2 + 1 = 4 * (m * m + m) + 2 := by rw [hm]; ring
    omega
  · have := odd_pow_add_one_two_pow (n := p) hy3 hyo hqo (by omega)
    omega

/-- **Base `2` on the right**: the only perfect power that is one more than a power of two
(with all exponents `> 1`) is `9 = 2 ^ 3 + 1`. -/
theorem isCatalanPair_two_right (x p q : ℕ) (h : IsCatalanPair x p 2 q) :
    x = 3 ∧ p = 2 ∧ q = 3 := by
  obtain ⟨hx, hp, -, hq, h⟩ := h
  have h2q : (2 : ℕ) ^ q % 2 = 0 := by
    have : (2 : ℕ) ^ q = 2 * 2 ^ (q - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hxo : Odd x := by
    rw [Nat.odd_iff]
    by_contra hc
    have hex : Even x := Nat.even_iff.2 (by omega)
    have : Even (x ^ p) := Nat.even_pow.2 ⟨hex, by omega⟩
    rw [Nat.even_iff] at this
    omega
  have hx3 : 3 ≤ x := by rcases hxo with ⟨m, hm⟩; omega
  rcases Nat.even_or_odd p with ⟨k, hk⟩ | hpo
  · -- `p` even: `u = x ^ k` satisfies `(u - 1) (u + 1) = 2 ^ q`, forcing `u = 3`.
    have hk1 : 1 ≤ k := by omega
    have hu : (x ^ k) ^ 2 = 2 ^ q + 1 := by
      rw [← pow_mul, show k * 2 = p by omega]; exact h
    obtain ⟨m, hm⟩ : Odd (x ^ k) := hxo.pow
    have hxk3 : 3 ≤ x ^ k := le_trans hx3 (Nat.le_self_pow (by omega) x)
    have hfac : 4 * (m * (m + 1)) = 2 ^ q := by
      have h1 : (x ^ k) ^ 2 = 4 * (m * m + m) + 1 := by rw [hm]; ring
      have h2 : 4 * (m * (m + 1)) = 4 * (m * m + m) := by ring
      omega
    have hdm : m ∣ 2 ^ q := ⟨4 * (m + 1), by rw [← hfac]; ring⟩
    have hdm1 : (m + 1) ∣ 2 ^ q := ⟨4 * m, by rw [← hfac]; ring⟩
    have hmodd : Odd m := by
      rcases Nat.even_or_odd m with he | ho
      · exact absurd (eq_one_of_odd_of_dvd_two_pow (Even.add_one he) hdm1) (by omega)
      · exact ho
    have hm1 : m = 1 := eq_one_of_odd_of_dvd_two_pow hmodd hdm
    subst hm1
    have hq3 : q = 3 := Nat.pow_right_injective (le_refl 2) (show 2 ^ q = 2 ^ 3 by omega)
    obtain ⟨hk1', hx3'⟩ :=
      exponent_eq_one_of_pow_lt_four hx (c := 3) (by norm_num) (by norm_num) (by omega)
    exact ⟨hx3', by omega, hq3⟩
  · exact absurd (odd_pow_sub_one_two_pow (n := q) hx3 hxo hpo h) (by omega)

/-! ### Reduction to the core case -/

/-- The *core case* of Catalan's conjecture: there is no solution of `x ^ p = y ^ q + 1` with
distinct prime exponents `p ≠ q` and both bases at least `3`.  This is the part of
Mihailescu's theorem that is not elementary. -/
def CatalanCoreCase : Prop :=
  ∀ x p y q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q → 3 ≤ x → 3 ≤ y → x ^ p ≠ y ^ q + 1

/-- **Catalan–Mihailescu**, reduced to the core case: assuming `CatalanCoreCase` (distinct prime
exponents, both bases `≥ 3`), the only pair of consecutive perfect powers is
`8 = 2 ^ 3`, `9 = 3 ^ 2`, i.e. any solution of `x ^ p - y ^ q = 1` with `x, y, p, q > 1`
has `x = 3`, `p = 2`, `y = 2`, `q = 3`.

The reduction replaces the exponents `p, q` by prime divisors `r ∣ p`, `s ∣ q` and the bases by
`x ^ (p / r)`, `y ^ (q / s)`; the cases with a base equal to `2` or with `r = s` are then settled
unconditionally by the base cases above. -/
theorem Catalan_Mihailescu (H : CatalanCoreCase) (x p y q : ℕ) (h : IsCatalanPair x p y q) :
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by
  obtain ⟨hx, hp, hy, hq, heq⟩ := h
  obtain ⟨r, hr, hrp⟩ := Nat.exists_prime_and_dvd (show p ≠ 1 by omega)
  obtain ⟨s, hs, hsq⟩ := Nat.exists_prime_and_dvd (show q ≠ 1 by omega)
  set a := p / r with hadef
  set b := q / s with hbdef
  have ha : a * r = p := Nat.div_mul_cancel hrp
  have hb : b * s = q := Nat.div_mul_cancel hsq
  have ha0 : a ≠ 0 := by intro h0; rw [h0, zero_mul] at ha; omega
  have hb0 : b ≠ 0 := by intro h0; rw [h0, zero_mul] at hb; omega
  have hX1 : 1 < x ^ a := Nat.one_lt_pow ha0 hx
  have hY1 : 1 < y ^ b := Nat.one_lt_pow hb0 hy
  have hmain : (x ^ a) ^ r = (y ^ b) ^ s + 1 := by
    rw [← pow_mul, ← pow_mul, ha, hb]; exact heq
  have hr1 : 1 < r := hr.one_lt
  have hs1 : 1 < s := hs.one_lt
  by_cases hX2 : x ^ a = 2
  · exact absurd (show IsCatalanPair 2 r (y ^ b) s from
      ⟨by norm_num, hr1, hY1, hs1, by rw [← hX2]; exact hmain⟩) (not_isCatalanPair_two_left _ _ _)
  by_cases hY2 : y ^ b = 2
  · obtain ⟨hX3, hr2, hs3⟩ := isCatalanPair_two_right (x ^ a) r s
      ⟨hX1, hr1, by norm_num, hs1, by rw [← hY2]; exact hmain⟩
    obtain ⟨ha1, hx3⟩ := exponent_eq_one_of_pow_lt_four hx (by norm_num) (by norm_num) hX3
    obtain ⟨hb1, hy2⟩ := exponent_eq_one_of_pow_lt_four hy (by norm_num) (by norm_num) hY2
    refine ⟨hx3, ?_, hy2, ?_⟩
    · rw [← ha, ha1, hr2, one_mul]
    · rw [← hb, hb1, hs3, one_mul]
  by_cases hrs : r = s
  · subst hrs
    exact absurd (show IsCatalanPair (x ^ a) r (y ^ b) r from ⟨hX1, hr1, hY1, hr1, hmain⟩)
      (not_isCatalanPair_of_eq_exponents _ _ _)
  · exact absurd hmain (H _ _ _ _ hr hs hrs (by omega) (by omega))

end Frontier


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

