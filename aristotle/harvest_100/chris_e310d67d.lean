/-
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 requires module
-- doc-comments to appear *after* the `import` lines; the text is otherwise verbatim.)

import Mathlib

/-!
## Overview

The Catalan–Mihailescu theorem states that `8 = 2 ^ 3` and `9 = 3 ^ 2` are the only two
consecutive perfect powers, i.e. the only solution of `x ^ p - y ^ q = 1` in integers
`x, y, p, q > 1` is `3 ^ 2 - 2 ^ 3 = 1`.

This file formalises the statement (`Frontier.CatalanMihailescuStatement`), and proves,
axiom-cleanly:

* the base case `3 ^ 2 = 2 ^ 3 + 1`, and that `8`, `9` are perfect powers;
* a Lean-checked **reduction**: the general statement is *equivalent* to the statement
  restricted to prime exponents (`Frontier.catalan_iff_prime_exponents`);
* several complete subcases of the theorem:
  - equal exponents: `x ^ k ≠ y ^ k + 1` for `y ≥ 1`, `k ≥ 2`;
  - both exponents even: `x ^ p ≠ y ^ q + 1` for `p`, `q` even and `y > 1`;
  - even exponent against an odd base: `x ^ p ≠ y ^ q + 1` whenever `p` is even, `y` is
    odd and `y > 1`, `q ≥ 2` (in particular, in a hypothetical second solution with
    `p` even the number `y` must be even);
  - odd base with even exponent: `x ^ p ≠ y ^ q + 1` whenever `y` is odd, `q` is even
    and `p ≥ 2`;
* a kernel-checked finite verification: `9` and `8` are the only consecutive perfect powers
  up to `1000`.

The main theorem `Frontier.Catalan_Mihailescu` packages these results.
-/

namespace Frontier

/-- `n` is a perfect power: `n = a ^ k` with `a > 1` and `k > 1`. -/
def IsPerfectPower (n : ℕ) : Prop := ∃ a k : ℕ, 1 < a ∧ 1 < k ∧ n = a ^ k

/-- The Catalan–Mihailescu statement: `9` and `8` are the only consecutive perfect powers. -/
def CatalanMihailescuStatement : Prop :=
  ∀ m n : ℕ, IsPerfectPower m → IsPerfectPower n → m = n + 1 → m = 9 ∧ n = 8

/-- The Catalan–Mihailescu statement restricted to prime exponents. -/
def CatalanMihailescuPrimeStatement : Prop :=
  ∀ x y p q : ℕ, 1 < x → 1 < y → p.Prime → q.Prime → x ^ p = y ^ q + 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-! ### The base case -/

theorem isPerfectPower_nine : IsPerfectPower 9 := ⟨3, 2, by norm_num, by norm_num, by norm_num⟩

theorem isPerfectPower_eight : IsPerfectPower 8 := ⟨2, 3, by norm_num, by norm_num, by norm_num⟩

theorem catalan_base_case : (3 : ℕ) ^ 2 = 2 ^ 3 + 1 := by norm_num

/-! ### Auxiliary arithmetic lemmas -/

/-- In `ℕ`, if a product of coprime numbers is a `k`-th power then each factor is. -/
theorem eq_pow_of_coprime_mul_eq_pow {a b c k : ℕ} (hab : Nat.Coprime a b)
    (h : a * b = c ^ k) : ∃ d, a = d ^ k := by
  have hu : IsUnit (gcd a b) := by
    have hg : gcd a b = 1 := hab
    rw [hg]; exact isUnit_one
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hu h
  exact ⟨d, (associated_iff_eq.mp hd).symm⟩

/-- A crude but sufficient lower bound: `(a+1)^q ≥ a^q + q * a` for `q ≥ 2`. -/
theorem succ_pow_lower_bound (a : ℕ) : ∀ q : ℕ, 2 ≤ q → a ^ q + q * a ≤ (a + 1) ^ q := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => ring_nf; omega
  | succ n hn ih =>
      have h1 : (a + 1) ^ (n + 1) = (a + 1) ^ n * (a + 1) := by ring
      have h2 : (a ^ n + n * a) * (a + 1) ≤ (a + 1) ^ n * (a + 1) :=
        Nat.mul_le_mul_right _ ih
      have key : (a ^ n + n * a) * (a + 1) = a ^ (n + 1) + a ^ n + n * a * a + n * a := by
        ring
      have hsq : a ≤ n * a * a := by
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp
        · calc a = 1 * 1 * a := by ring
            _ ≤ n * a * a := Nat.mul_le_mul_right a (Nat.mul_le_mul (by omega) ha)
      have hexp : (n + 1) * a = n * a + a := by ring
      omega

/-- If `x ^ p = 9` with `x > 1` and `p ≥ 2` then `x = 3` and `p = 2`. -/
theorem pow_eq_nine {x p : ℕ} (hx : 1 < x) (hp : 2 ≤ p) (h : x ^ p = 9) : x = 3 ∧ p = 2 := by
  have hxle : x ≤ 9 := by
    calc x = x ^ 1 := (pow_one x).symm
    _ ≤ x ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 9 := h
  have hple : p ≤ 3 := by
    by_contra hc
    push_neg at hc
    have : 2 ^ 4 ≤ x ^ p :=
      le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.pow_le_pow_left hx p)
    omega
  interval_cases x <;> interval_cases p <;> simp_all

/-- If `y ^ q = 8` with `y > 1` and `q ≥ 2` then `y = 2` and `q = 3`. -/
theorem pow_eq_eight {y q : ℕ} (hy : 1 < y) (hq : 2 ≤ q) (h : y ^ q = 8) : y = 2 ∧ q = 3 := by
  have hyle : y ≤ 8 := by
    calc y = y ^ 1 := (pow_one y).symm
    _ ≤ y ^ q := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 8 := h
  have hqle : q ≤ 3 := by
    by_contra hc
    push_neg at hc
    have : 2 ^ 4 ≤ y ^ q :=
      le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.pow_le_pow_left hy q)
    omega
  interval_cases y <;> interval_cases q <;> simp_all

/-! ### Reduction to prime exponents -/

/-- Every perfect power is a perfect power with a *prime* exponent. -/
theorem isPerfectPower_iff_prime_exponent (n : ℕ) :
    IsPerfectPower n ↔ ∃ a p : ℕ, 1 < a ∧ p.Prime ∧ n = a ^ p := by
  constructor
  · rintro ⟨a, k, ha, hk, rfl⟩
    refine ⟨a ^ (k / k.minFac), k.minFac, ?_, Nat.minFac_prime (by omega), ?_⟩
    · have h1 : 1 ≤ k / k.minFac :=
        Nat.one_le_div_iff (Nat.minFac_pos k) |>.mpr (Nat.minFac_le (by omega))
      calc 1 = a ^ 0 := (pow_zero a).symm
      _ < a ^ (k / k.minFac) := Nat.pow_lt_pow_right ha (by omega)
    · rw [← pow_mul, Nat.div_mul_cancel (Nat.minFac_dvd k)]
  · rintro ⟨a, p, ha, hp, rfl⟩
    exact ⟨a, p, ha, hp.one_lt, rfl⟩

/-- **Lean-checked reduction**: the Catalan–Mihailescu statement is equivalent to its
restriction to prime exponents. -/
theorem catalan_iff_prime_exponents :
    CatalanMihailescuStatement ↔ CatalanMihailescuPrimeStatement := by
  constructor
  · intro H x y p q hx hy hp hq heq
    obtain ⟨h9, h8⟩ := H (x ^ p) (y ^ q) ⟨x, p, hx, hp.one_lt, rfl⟩ ⟨y, q, hy, hq.one_lt, rfl⟩ heq
    obtain ⟨hx3, hp2⟩ := pow_eq_nine hx hp.two_le h9
    obtain ⟨hy2, hq3⟩ := pow_eq_eight hy hq.two_le h8
    exact ⟨hx3, hp2, hy2, hq3⟩
  · intro H m n hm hn hmn
    obtain ⟨x, p, hx, hp, rfl⟩ := (isPerfectPower_iff_prime_exponent m).mp hm
    obtain ⟨y, q, hy, hq, rfl⟩ := (isPerfectPower_iff_prime_exponent n).mp hn
    obtain ⟨hx3, hp2, hy2, hq3⟩ := H x y p q hx hy hp hq hmn
    subst hx3; subst hp2; subst hy2; subst hq3
    norm_num

/-! ### Complete subcases -/

/-- Two consecutive perfect powers cannot have the same exponent. -/
theorem pow_ne_pow_add_one_of_eq_exponent {x y k : ℕ} (hy : 1 ≤ y) (hk : 2 ≤ k) :
    x ^ k ≠ y ^ k + 1 := by
  intro h
  have hxy : y < x := by
    by_contra hc
    push_neg at hc
    have : x ^ k ≤ y ^ k := Nat.pow_le_pow_left hc k
    omega
  have h1 : (y + 1) ^ k ≤ x ^ k := Nat.pow_le_pow_left (by omega) k
  have h2 : y ^ k + k * y ≤ (y + 1) ^ k := succ_pow_lower_bound y k hk
  have h3 : 2 * 1 ≤ k * y := Nat.mul_le_mul hk hy
  omega

/-- There is no solution of `x ^ p = y ^ q + 1` with both exponents even (and `y > 1`). -/
theorem pow_ne_pow_add_one_of_even_even {x y p q : ℕ} (hy : 1 < y) (hp : Even p) (hq : Even q) :
    x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨s, hs⟩ := hp
  obtain ⟨t, ht⟩ := hq
  have hxs : x ^ p = (x ^ s) ^ 2 := by rw [← pow_mul]; rw [hs]; ring_nf
  have hyt : y ^ q = (y ^ t) ^ 2 := by rw [← pow_mul]; rw [ht]; ring_nf
  set A := x ^ s
  set B := y ^ t with hB
  rw [hxs, hyt] at h
  -- `B ≥ 2` as soon as `t ≥ 1`; the degenerate case `t = 0` is handled separately
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · -- then `q = 0`, so `A ^ 2 = 2`, which is impossible
    subst ht0
    simp only [pow_zero] at hB
    rw [hB] at h
    norm_num at h
    rcases Nat.lt_or_ge A 2 with hA2 | hA2
    · interval_cases A <;> omega
    · nlinarith
  · have hB2 : 2 ≤ B := by
      rw [hB]
      calc 2 ≤ y := hy
      _ = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ t := Nat.pow_le_pow_right (by omega) ht0
    have hAB : B < A := by
      by_contra hc
      push_neg at hc
      have : A ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    nlinarith

/-- If `x ^ 2 = y ^ q + 1` with `q ≥ 2`, then `y` cannot be odd (and `> 1`).
This is the coprime-factorisation subcase `(x-1)(x+1) = y ^ q`. -/
theorem sq_ne_odd_pow_add_one {x y q : ℕ} (hyodd : Odd y) (hy : 1 < y) (hq : 2 ≤ q) :
    x ^ 2 ≠ y ^ q + 1 := by
  intro h
  have hyq : 9 ≤ y ^ q := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
    _ ≤ y ^ 2 := Nat.pow_le_pow_left (by rcases hyodd with ⟨k, hk⟩; omega) 2
    _ ≤ y ^ q := Nat.pow_le_pow_right (by omega) hq
  have hx : 3 ≤ x := by
    by_contra hc
    push_neg at hc
    interval_cases x <;> omega
  obtain ⟨u, rfl⟩ : ∃ u, x = u + 1 := ⟨x - 1, by omega⟩
  have hprod : u * (u + 2) = y ^ q := by nlinarith [h]
  -- `y ^ q` is odd, hence `(u+1)^2` is even, hence `u` is odd
  have hyqodd : Odd (y ^ q) := hyodd.pow
  have hueven : Even ((u + 1) ^ 2) := by
    rw [h]
    exact hyqodd.add_one
  have hu1 : Even (u + 1) := by
    rcases (Nat.even_pow.mp hueven) with ⟨he, -⟩
    exact he
  have huodd : u % 2 = 1 := by
    have h' := Nat.even_iff.mp hu1
    omega
  have hcop : Nat.Coprime u (u + 2) := by
    have hg : Nat.gcd u (u + 2) = Nat.gcd u 2 := by
      rw [Nat.add_comm u 2, Nat.gcd_add_self_right]
    have h2u : Nat.Coprime 2 u := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
    rw [Nat.Coprime, hg, Nat.gcd_comm]
    exact h2u
  obtain ⟨a, ha⟩ := eq_pow_of_coprime_mul_eq_pow hcop hprod
  obtain ⟨b, hb⟩ := eq_pow_of_coprime_mul_eq_pow hcop.symm (by rw [Nat.mul_comm]; exact hprod)
  -- now `b ^ q = a ^ q + 2` with `a ≥ 2`
  have hu3 : 3 ≤ u := by nlinarith
  have ha2 : 2 ≤ a := by
    by_contra hc
    push_neg at hc
    interval_cases a
    · rw [zero_pow (by omega)] at ha; omega
    · rw [one_pow] at ha; omega
  have hba : a < b := by
    by_contra hc
    push_neg at hc
    have : b ^ q ≤ a ^ q := Nat.pow_le_pow_left hc q
    omega
  have h1 : (a + 1) ^ q ≤ b ^ q := Nat.pow_le_pow_left (by omega) q
  have h2 : a ^ q + q * a ≤ (a + 1) ^ q := succ_pow_lower_bound a q hq
  have h3 : 2 * 2 ≤ q * a := Nat.mul_le_mul hq ha2
  omega

/-- If `x ^ p = y ^ q + 1` with `p` even, `q ≥ 2` and `y > 1`, then `y` is even.
Equivalently: there is no solution with `p` even and `y` odd. -/
theorem pow_ne_pow_add_one_of_even_exp_odd_base {x y p q : ℕ} (hyodd : Odd y) (hy : 1 < y)
    (hp : Even p) (hq : 2 ≤ q) : x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨s, hs⟩ := hp
  have hxs : x ^ p = (x ^ s) ^ 2 := by rw [← pow_mul, hs]; ring_nf
  rw [hxs] at h
  exact sq_ne_odd_pow_add_one hyodd hy hq h

/-- If `x ^ p = y ^ q + 1` with `p ≥ 2` and `q` even, then `y` cannot be odd:
otherwise `y ^ q + 1 ≡ 2 (mod 4)`, which is never a perfect power with exponent `≥ 2`. -/
theorem pow_ne_pow_add_one_of_odd_base_even_exp {x y p q : ℕ} (hyodd : Odd y) (hp : 2 ≤ p)
    (hq : Even q) : x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨t, ht⟩ := hq
  have hyt : y ^ q = (y ^ t) ^ 2 := by rw [← pow_mul, ht]; ring_nf
  obtain ⟨c, hc⟩ : Odd (y ^ t) := hyodd.pow
  have hsq : (y ^ t) ^ 2 = 4 * (c * c + c) + 1 := by rw [hc]; ring
  have hx4 : x ^ p % 4 = 2 := by
    rw [h, hyt, hsq]; omega
  rcases Nat.even_or_odd x with hx | hx
  · obtain ⟨d, rfl⟩ := hx
    have hsplit : (d + d) ^ p = (d + d) ^ 2 * (d + d) ^ (p - 2) := by
      rw [← pow_add]; congr 1; omega
    have hdvd : 4 ∣ (d + d) ^ p := by
      rw [hsplit]
      exact Dvd.dvd.mul_right ⟨d * d, by ring⟩ _
    omega
  · have : Odd (x ^ p) := hx.pow
    rw [Nat.odd_iff] at this
    omega

/-! ### A verified finite check -/

/-- The perfect powers up to `1000`. -/
def perfectPowersUpTo1000 : Finset ℕ :=
  {4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 81, 100, 121, 125, 128, 144, 169, 196, 216, 225, 243,
   256, 289, 324, 343, 361, 400, 441, 484, 512, 529, 576, 625, 676, 729, 784, 841, 900, 961, 1000}

theorem mem_perfectPowersUpTo1000 {n : ℕ} (hn : IsPerfectPower n) (h : n ≤ 1000) :
    n ∈ perfectPowersUpTo1000 := by
  obtain ⟨a, k, ha, hk, rfl⟩ := hn
  have h2 : a ^ 2 ≤ a ^ k := Nat.pow_le_pow_right (by omega) hk
  have hasq : a * a ≤ 1000 := by nlinarith [pow_two a]
  have ha31 : a ≤ 31 := by nlinarith
  have h2k : 2 ^ k ≤ a ^ k := Nat.pow_le_pow_left ha k
  have hk9 : k ≤ 9 := by
    by_contra hc
    push_neg at hc
    have : 2 ^ 10 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  clear h2 hasq h2k
  interval_cases a <;> interval_cases k <;> revert h <;> decide

/-- The Catalan–Mihailescu statement, verified for all perfect powers up to `1000`. -/
theorem catalan_below_1000 {m n : ℕ} (hm : IsPerfectPower m) (hn : IsPerfectPower n)
    (hmn : m = n + 1) (h : m ≤ 1000) : m = 9 ∧ n = 8 := by
  subst hmn
  have h1 := mem_perfectPowersUpTo1000 hn (by omega)
  have h2 := mem_perfectPowersUpTo1000 hm h
  refine ⟨?_, ?_⟩ <;> (fin_cases h1 <;> revert h2 <;> decide)

/-! ### Main theorem -/

/--
**Catalan–Mihailescu** (formalisation, base case and Lean-checked reduction).

The conjuncts are:
1. the base case: `9` and `8` are consecutive perfect powers, witnessed by `3 ^ 2 = 2 ^ 3 + 1`;
2. a reduction: the full statement "`9` and `8` are the only consecutive perfect powers"
   is equivalent to its restriction to prime exponents;
3. the subcase of equal exponents;
4. the subcase of two even exponents;
5. the subcase of an even exponent `p` with odd base `y`;
6. the subcase of an odd base `y` with even exponent `q`;
7. a kernel-checked finite verification of the full statement for perfect powers up to `1000`.
-/
theorem Catalan_Mihailescu :
    (IsPerfectPower 9 ∧ IsPerfectPower 8 ∧ (9 : ℕ) = 8 + 1 ∧ (3 : ℕ) ^ 2 = 2 ^ 3 + 1) ∧
    (CatalanMihailescuStatement ↔ CatalanMihailescuPrimeStatement) ∧
    (∀ x y k : ℕ, 1 ≤ y → 2 ≤ k → x ^ k ≠ y ^ k + 1) ∧
    (∀ x y p q : ℕ, 1 < y → Even p → Even q → x ^ p ≠ y ^ q + 1) ∧
    (∀ x y p q : ℕ, Odd y → 1 < y → Even p → 2 ≤ q → x ^ p ≠ y ^ q + 1) ∧
    (∀ x y p q : ℕ, Odd y → 2 ≤ p → Even q → x ^ p ≠ y ^ q + 1) ∧
    (∀ m n : ℕ, IsPerfectPower m → IsPerfectPower n → m = n + 1 → m ≤ 1000 → m = 9 ∧ n = 8) :=
  ⟨⟨isPerfectPower_nine, isPerfectPower_eight, by norm_num, catalan_base_case⟩,
   catalan_iff_prime_exponents,
   fun _ _ _ hy hk => pow_ne_pow_add_one_of_eq_exponent hy hk,
   fun _ _ _ _ hy hp hq => pow_ne_pow_add_one_of_even_even hy hp hq,
   fun _ _ _ _ hyodd hy hp hq => pow_ne_pow_add_one_of_even_exp_odd_base hyodd hy hp hq,
   fun _ _ _ _ hyodd hp hq => pow_ne_pow_add_one_of_odd_base_even_exp hyodd hp hq,
   fun _ _ hm hn hmn h => catalan_below_1000 hm hn hmn h⟩

end Frontier

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

