import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
