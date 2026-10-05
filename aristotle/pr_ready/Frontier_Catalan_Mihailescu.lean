/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Statement: 8 and 9 are the only consecutive perfect powers (x^p − y^q = 1 ⇒ 3²−2³).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a file,
so the mandated header comment appears immediately after `import Mathlib`.

## Contents

The Catalan–Mihailescu theorem states that `8 = 2 ^ 3` and `9 = 3 ^ 2` are the only two
consecutive perfect powers, i.e. that the only solution of `x ^ p = y ^ q + 1` in integers
`x, y > 1`, `p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`.

This file contains:

* `Frontier.CatalanMihailescu` : the formal statement of the theorem.
* `Frontier.CatalanMihailescuPrimeExponents` : a restricted statement, where the two exponents
  are additionally assumed to be *distinct primes* and the pair of exponents is assumed to be
  different from `(3, 2)`.
* `Frontier.Catalan_Mihailescu` : the **Lean-checked reduction**, namely that the two statements
  above are equivalent. The nontrivial direction uses two unconditionally proved special cases:
  - `Frontier.pow_ne_pow_add_one` : `x ^ n ≠ y ^ n + 1` for `x, y > 1` and `n > 1`
    (equal exponents);
  - `Frontier.cube_ne_sq_add_one` : `x ^ 3 ≠ y ^ 2 + 1` for `y > 0`, i.e. no perfect cube is one
    more than a positive perfect square (the case `(p, q) = (3, 2)`; this is the case `n = 3` of
    a theorem of V. A. Lebesgue). It is proved here by unique factorization in the Gaussian
    integers `ℤ[i]`.
* `Frontier.catalan_base_case` : the base case `3 ^ 2 = 2 ^ 3 + 1`.
-/

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

set_option grind.warning false

namespace Frontier

/-! ## Units of the Gaussian integers -/

/-- Every unit of `ℤ[i]` has order dividing `4`. -/
theorem gaussianInt_isUnit_pow_four (u : GaussianInt) (hu : IsUnit u) : u ^ 4 = 1 := by
  have h : u.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
  have hnorm : u.norm = u.re ^ 2 + u.im ^ 2 := by simp [Zsqrtd.norm]; ring
  have hn : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h0 : (0 : ℤ) ≤ u.norm := by rw [hnorm]; positivity
    omega
  obtain ⟨a, b⟩ := u
  simp only at hn
  have ha : -1 ≤ a ∧ a ≤ 1 := ⟨by nlinarith [sq_nonneg b], by nlinarith [sq_nonneg b]⟩
  have hb : -1 ≤ b ∧ b ≤ 1 := ⟨by nlinarith [sq_nonneg a], by nlinarith [sq_nonneg a]⟩
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  interval_cases a <;> interval_cases b <;> simp_all [Zsqrtd.ext_iff, pow_succ]

/-! ## No cube is one more than a positive square -/

/-- **Lebesgue's theorem for exponent three.**  The only integer solutions of `x ^ 3 = y ^ 2 + 1`
have `y = 0`.  The proof factors `y + i` and `y - i` in the Gaussian integers. -/
theorem int_cube_eq_sq_add_one (x y : ℤ) (h : x ^ 3 = y ^ 2 + 1) : y = 0 := by
  -- Step 1: `y` is even (otherwise `y ^ 2 + 1 ≡ 2 [ZMOD 4]` while `x ^ 3` is not).
  obtain ⟨m, hm⟩ : ∃ m, y = 2 * m := by
    rcases Int.even_or_odd y with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k, by omega⟩
    · exfalso
      have hx : Even x := by
        have hev : Even (x ^ 3) := by rw [h, hk]; exact ⟨2 * k ^ 2 + 2 * k + 1, by ring⟩
        exact (Int.even_pow.mp hev).1
      obtain ⟨t, ht⟩ := hx
      subst hk ht
      have h4 : 4 * t ^ 3 = 2 * k ^ 2 + 2 * k + 1 := by nlinarith [h]
      have h2 : (2 : ℤ) ∣ 1 := ⟨2 * t ^ 3 - k ^ 2 - k, by linarith⟩
      norm_num at h2
  set A : GaussianInt := ⟨y, 1⟩ with hA
  set B : GaussianInt := ⟨y, -1⟩ with hB
  -- Step 2: `y + i` and `y - i` are coprime in `ℤ[i]` (an explicit Bézout identity).
  have hcop : IsCoprime A B := by
    refine ⟨(⟨m ^ 2, 0⟩ : GaussianInt) * A - 2 * (⟨m ^ 2, 0⟩ : GaussianInt) * B + B,
            (⟨m ^ 2, 0⟩ : GaussianInt) * B, ?_⟩
    rw [hA, hB]; subst hm
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
  have hmul : A * B = (⟨x, 0⟩ : GaussianInt) ^ 3 := by
    rw [hA, hB]
    ext
    · simp [Zsqrtd.re_mul, Zsqrtd.im_mul, pow_succ]; nlinarith [h]
    · simp [Zsqrtd.re_mul, Zsqrtd.im_mul, pow_succ]
  -- Step 3: hence `y + i` is a cube up to a unit, and every unit of `ℤ[i]` is a cube.
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hcop hmul
  set w : GaussianInt := d * (u : GaussianInt) ^ 3 with hw
  have hu4 : (u : GaussianInt) ^ 4 = 1 := gaussianInt_isUnit_pow_four _ u.isUnit
  have hw3 : w ^ 3 = A := by
    rw [hw, mul_pow, ← hu,
      show ((u : GaussianInt) ^ 3) ^ 3 = ((u : GaussianInt) ^ 4) ^ 2 * (u : GaussianInt) by ring,
      hu4]
    ring
  -- Step 4: compare real and imaginary parts.
  have him : 3 * w.re ^ 2 * w.im - w.im ^ 3 = 1 := by
    have hc := congrArg Zsqrtd.im hw3
    simp only [hA] at hc
    rw [show (w ^ 3).im = 3 * w.re ^ 2 * w.im - w.im ^ 3 by
      simp [pow_succ, Zsqrtd.im_mul, Zsqrtd.re_mul]; ring] at hc
    exact hc
  have hre : w.re ^ 3 - 3 * w.re * w.im ^ 2 = y := by
    have hc := congrArg Zsqrtd.re hw3
    simp only [hA] at hc
    rw [show (w ^ 3).re = w.re ^ 3 - 3 * w.re * w.im ^ 2 by
      simp [pow_succ, Zsqrtd.im_mul, Zsqrtd.re_mul]; ring] at hc
    exact hc
  have hdvd : w.im ∣ 1 := ⟨3 * w.re ^ 2 - w.im ^ 2, by linarith [him]⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with hb | hb
  · exfalso
    rw [hb] at him
    have h3 : (3 : ℤ) ∣ 2 := ⟨w.re ^ 2, by linarith⟩
    norm_num at h3
  · rw [hb] at him
    have ha0 : w.re = 0 := by nlinarith [him, sq_nonneg w.re]
    rw [← hre, ha0]; ring

/-- No perfect cube is one more than a positive perfect square. -/
theorem cube_ne_sq_add_one (x y : ℕ) (hy : 0 < y) : x ^ 3 ≠ y ^ 2 + 1 := by
  intro h
  have hz : (x : ℤ) ^ 3 = (y : ℤ) ^ 2 + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
  have := int_cube_eq_sq_add_one (x : ℤ) (y : ℤ) hz
  omega

/-! ## Equal exponents -/

private theorem succ_pow_ge (y : ℕ) (hy : 2 ≤ y) :
    ∀ n, 2 ≤ n → y ^ n + 2 ≤ (y + 1) ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => nlinarith
  | succ n hn ih =>
      have hy1 : y ^ n + 2 ≤ (y + 1) ^ n := ih
      calc y ^ (n + 1) + 2 ≤ (y ^ n + 2) * (y + 1) := by
            have : 1 ≤ y ^ n := Nat.one_le_pow _ _ (by omega)
            ring_nf
            nlinarith [this]
        _ ≤ (y + 1) ^ n * (y + 1) := by exact Nat.mul_le_mul_right _ hy1
        _ = (y + 1) ^ (n + 1) := by ring

/-- Two perfect powers with the same exponent `n > 1` are never consecutive, as soon as the
smaller base satisfies `y > 1`. -/
theorem pow_ne_pow_add_one (x y n : ℕ) (hy : 1 < y) (hn : 1 < n) :
    x ^ n ≠ y ^ n + 1 := by
  intro h
  have hlt : y ^ n < x ^ n := by omega
  have hxy : y < x := by
    by_contra hc
    exact absurd (Nat.pow_le_pow_left (by omega : x ≤ y) n) (by omega)
  have h1 : (y + 1) ^ n ≤ x ^ n := Nat.pow_le_pow_left (by omega) n
  have h2 : y ^ n + 2 ≤ (y + 1) ^ n := succ_pow_ge y hy n hn
  omega

/-! ## The case of the bases `3` and `2` (Levi ben Gerson) -/

/-- **Levi ben Gerson's theorem** (in the form needed here): the only powers of `3` and of `2`
with exponents `> 1` that are consecutive are `9 = 3 ^ 2` and `8 = 2 ^ 3`. -/
theorem three_pow_eq_two_pow_add_one (p q : ℕ) (hp : 1 < p) (hq : 1 < q)
    (h : 3 ^ p = 2 ^ q + 1) : p = 2 ∧ q = 3 := by
  have h4 : (2 : ℕ) ^ q % 4 = 0 := by
    obtain ⟨c, rfl⟩ : ∃ c, q = c + 2 := ⟨q - 2, by omega⟩
    rw [pow_add]
    omega
  -- `p` is even, since `3 ^ p ≡ 1 [MOD 4]`
  obtain ⟨t, rfl⟩ : ∃ t, p = 2 * t := by
    rcases Nat.even_or_odd p with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t, by omega⟩
    · exfalso
      have h3 : (3 : ℕ) ^ p % 4 = 3 := by
        subst ht
        rw [pow_succ, pow_mul]
        have h9 : ((3 : ℕ) ^ 2) ^ t % 4 = 1 := by rw [Nat.pow_mod]; norm_num
        omega
      omega
  have ht1 : 1 ≤ t := by omega
  have hu3 : 3 ≤ 3 ^ t := by
    calc (3 : ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht1
  have husq : (3 : ℕ) ^ t * 3 ^ t = 2 ^ q + 1 := by
    rw [← pow_add, show t + t = 2 * t by ring]; exact h
  -- `(3 ^ t - 1) * (3 ^ t + 1) = 2 ^ q`, so both factors are powers of two
  obtain ⟨a, ha⟩ : ∃ a, (3 : ℕ) ^ t = a + 1 := ⟨3 ^ t - 1, by omega⟩
  have hfac : a * (a + 2) = 2 ^ q := by rw [ha] at husq; nlinarith [husq]
  have ha2 : 2 ≤ a := by omega
  obtain ⟨i, hiq, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (⟨a + 2, hfac.symm⟩ : a ∣ 2 ^ q)
  obtain ⟨j, hjq, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (⟨a, by rw [← hfac]; ring⟩ : (a + 2) ∣ 2 ^ q)
  have hieq : i = 1 := by
    by_contra hne
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | h'
      · simp at hi; omega
      · exact h'
    have hi2 : 2 ≤ i := by omega
    have h4i : (4 : ℕ) ∣ a := by
      rw [hi]; exact dvd_trans (by norm_num) (pow_dvd_pow 2 hi2)
    have hjbig : 4 < 2 ^ j := by omega
    have hj2 : 2 ≤ j := by
      by_contra hj'
      interval_cases j <;> omega
    have h4j : (4 : ℕ) ∣ a + 2 := by
      rw [hj]; exact dvd_trans (by norm_num) (pow_dvd_pow 2 hj2)
    omega
  have hae : a = 2 := by rw [hi, hieq]; norm_num
  have hu' : (3 : ℕ) ^ t = 3 ^ 1 := by rw [ha, hae]; norm_num
  have ht : t = 1 := Nat.pow_right_injective (by norm_num) hu'
  subst ht
  refine ⟨by norm_num, ?_⟩
  have hq3 : (2 : ℕ) ^ q = 2 ^ 3 := by rw [← hfac, hae]; norm_num
  exact Nat.pow_right_injective (le_refl 2) hq3

/-! ## The statement of the Catalan–Mihailescu theorem and its reduction -/

/-- The Catalan–Mihailescu theorem: `3 ^ 2 = 2 ^ 3 + 1` is the only way for two perfect powers
(with bases and exponents `> 1`) to be consecutive. -/
def CatalanMihailescu : Prop :=
  ∀ x y p q : ℕ, 1 < x → 1 < y → 1 < p → 1 < q → x ^ p = y ^ q + 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-- The reduced form of the Catalan–Mihailescu statement: there is no solution of
`x ^ p = y ^ q + 1` with `x, y > 1` whose exponents are **distinct primes** with `(p, q) ≠ (3, 2)`
and whose bases satisfy `(x, y) ≠ (3, 2)`. -/
def CatalanMihailescuReduced : Prop :=
  ∀ x y p q : ℕ, 1 < x → 1 < y → p.Prime → q.Prime → p ≠ q → ¬(p = 3 ∧ q = 2) →
    ¬(x = 3 ∧ y = 2) → x ^ p ≠ y ^ q + 1

/-- The base case: `9 = 3 ^ 2` and `8 = 2 ^ 3` are consecutive. -/
theorem catalan_base_case : (3 : ℕ) ^ 2 = 2 ^ 3 + 1 := by norm_num

/-- **Lean-checked reduction of the Catalan–Mihailescu theorem.**

The full statement is equivalent to the reduced non-existence statement
`Frontier.CatalanMihailescuReduced`.  In other words, in order to prove Catalan's conjecture it
suffices to rule out solutions whose exponents are distinct primes other than `(3, 2)` and whose
bases are not `(3, 2)`:

* composite exponents reduce to prime ones;
* equal exponents are impossible (`Frontier.pow_ne_pow_add_one`);
* the exponent pair `(3, 2)` is impossible (`Frontier.cube_ne_sq_add_one`, proved via unique
  factorization in the Gaussian integers);
* the base pair `(3, 2)` yields exactly the known solution `3 ^ 2 = 2 ^ 3 + 1`
  (`Frontier.three_pow_eq_two_pow_add_one`). -/
theorem Catalan_Mihailescu : CatalanMihailescu ↔ CatalanMihailescuReduced := by
  constructor
  · intro H x y p q hx hy hp hq _ _ hxy he
    obtain ⟨hx3, _, hy2, _⟩ := H x y p q hx hy hp.one_lt hq.one_lt he
    exact hxy ⟨hx3, hy2⟩
  · intro H x y p q hx hy hp hq he
    -- replace `p` and `q` by prime exponents
    obtain ⟨r, hrp, k, hk⟩ : ∃ r, Nat.Prime r ∧ ∃ k, p = r * k :=
      ⟨p.minFac, Nat.minFac_prime (by omega), p.minFac_dvd⟩
    obtain ⟨s, hsp, l, hl⟩ : ∃ s, Nat.Prime s ∧ ∃ l, q = s * l :=
      ⟨q.minFac, Nat.minFac_prime (by omega), q.minFac_dvd⟩
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
    have hl0 : l ≠ 0 := by rintro rfl; simp at hl; omega
    have hX : 1 < x ^ k := Nat.one_lt_pow hk0 hx
    have hY : 1 < y ^ l := Nat.one_lt_pow hl0 hy
    have hE : (x ^ k) ^ r = (y ^ l) ^ s + 1 := by
      rw [← pow_mul, ← pow_mul, mul_comm k r, mul_comm l s, ← hk, ← hl]; exact he
    have hrs : r ≠ s := by
      rintro rfl
      exact pow_ne_pow_add_one _ _ r hY hrp.one_lt hE
    have h32 : ¬(r = 3 ∧ s = 2) := by
      rintro ⟨rfl, rfl⟩
      exact cube_ne_sq_add_one (x ^ k) (y ^ l) (by omega) hE
    by_cases hb : x ^ k = 3 ∧ y ^ l = 2
    · -- the bases are `3` and `2`; Levi ben Gerson's theorem pins down the exponents
      obtain ⟨hX3, hY2⟩ := hb
      obtain ⟨hx3, hk1⟩ : x = 3 ∧ k = 1 := (Nat.Prime.pow_eq_iff (by norm_num)).mp hX3
      obtain ⟨hy2, hl1⟩ : y = 2 ∧ l = 1 := (Nat.Prime.pow_eq_iff (by norm_num)).mp hY2
      subst hx3; subst hy2
      obtain ⟨hp2, hq3⟩ := three_pow_eq_two_pow_add_one p q hp hq he
      exact ⟨rfl, hp2, rfl, hq3⟩
    · exact absurd hE (H (x ^ k) (y ^ l) r s hX hY hrp hsp hrs h32 hb)

end Frontier

