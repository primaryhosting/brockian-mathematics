import Mathlib

/-!
# Ramanujan's partition congruence `p(7n+5) ≡ 0 (mod 7)`

This file contains a self-contained proof of Ramanujan's congruence for the modulus `7`.

The strategy is the classical generating function argument:

* Let `E = ∏ (1 - X^i)` and `P = ∑ p(n) X^n = E⁻¹`.
* Jacobi's identity `E^3 = ∑_{j ≥ 0} (-1)^j (2j+1) X^{j(j+1)/2}` is proved from a finite form of
  the Jacobi triple product, obtained by induction on `n` from the `q`-Pascal recursion for
  Gaussian binomial coefficients, together with a dual-number ("derivative at `z = -1`")
  specialization and a limiting argument.
* In characteristic `7` one has `E^7 = ∏ (1 - X^{7i})`, so `P · E^7 = E^6 = (E^3)^2`, and the
  coefficients of `(E^3)^2` in degrees `≡ 5 (mod 7)` vanish mod `7` because `-1` is not a square
  mod `7`.
* A strong induction then gives `7 ∣ p(7n+5)`.
-/

namespace Brockian.Ramanujan7

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

/-! ## Gaussian binomial coefficients -/

section QB

variable {R : Type*} [CommRing R]

/-- The Gaussian binomial coefficient `[n choose k]_q`, defined by the `q`-Pascal recursion. -/

lemma coeff_JJ_sq_term (a b : ℕ) (hab : (a + b) % 7 = 5) : jcoef a * jcoef b = 0 := by
  by_cases ha : ∀ i, tri i ≠ a
  · rw [jcoef_eq_zero_of a ha]
    ring
  · push_neg at ha
    obtain ⟨i, hi⟩ := ha
    by_cases hb : ∀ j, tri j ≠ b
    · rw [jcoef_eq_zero_of b hb]
      ring
    · push_neg at hb
      obtain ⟨j, hj⟩ := hb
      rw [jcoef_eq a i hi, jcoef_eq b j hj]
      -- Need to show (-1)^i * (2*i+1) * ((-1)^j * (2*j+1)) = 0
      -- Key: (2*i+1)^2 + (2*j+1)^2 ≡ 0 (mod 7)
      have hmod : (8 * (a + b) + 2) % 7 = 0 := by omega
      have h1 : (8 : ℕ) * tri i + 1 = (2 * i + 1) ^ 2 := eight_tri_add_one i
      have h2 : (8 : ℕ) * tri j + 1 = (2 * j + 1) ^ 2 := eight_tri_add_one j
      have key : ((2 * i + 1 : ℕ) : ZMod 7) ^ 2 + ((2 * j + 1 : ℕ) : ZMod 7) ^ 2 = 0 := by
        have hsum : ((8 * tri i + 1) + (8 * tri j + 1) : ℕ) = 8 * (a + b) + 2 := by rw [hi, hj]; ring
        rw [h1, h2] at hsum
        norm_cast
        have hdiv : (7 : ℕ) ∣ (2 * i + 1) ^ 2 + (2 * j + 1) ^ 2 := by omega
        exact (ZMod.natCast_eq_zero_iff ((2 * i + 1) ^ 2 + (2 * j + 1) ^ 2) 7).mpr hdiv
      -- In ZMod 7, x^2 + y^2 = 0 implies x = 0 or y = 0
      have forbid : ∀ x y : ZMod 7, x ^ 2 + y ^ 2 = 0 → x = 0 ∨ y = 0 := by decide
      rcases forbid _ _ key with hx | hy
      · simp_all
      · simp_all

/-- The coefficients of `J^2` in degrees `≡ 5 (mod 7)` vanish. -/
