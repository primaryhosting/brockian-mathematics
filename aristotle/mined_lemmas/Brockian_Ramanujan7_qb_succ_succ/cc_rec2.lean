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

lemma cc_rec2 (q : R) (n k : ℕ) :
    cc q (n + 1) (k + 2)
      = (1 + q ^ (2 * n + 1)) * cc q n (k + 1) + q ^ n * cc q n (k + 2)
        + q ^ (n + 1) * cc q n k := by
  unfold cc
  -- Key exponent relations from ee
  have h_ee_shift : ee (n + 1) (k + 2) = ee n (k + 1) := ee_shift n (k + 1)
  -- Use qb_succ_succ and qb_pascal2 to expand
  rw [show 2 * (n + 1) = 2 * n + 2 by ring]
  rw [qb_succ_succ, qb_pascal2, qb_pascal2]
  rw [h_ee_shift]
  by_cases hk : k + 1 ≤ 2 * n
  · -- Case: k + 1 ≤ 2 * n
    have hk2 : k + 2 ≤ 2 * n + 1 := by omega
    -- Identity: q ^ (k + 2) * q ^ (2 * n - (k + 1)) = q ^ (2 * n + 1)
    have id1 : q ^ (k + 2) * q ^ (2 * n - (k + 1)) = q ^ (2 * n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    -- ee_down relations
    have id2 : ee n (k + 2) + (2 * n - (k + 1)) = n + 1 + ee n (k + 1) := ee_down n (k + 1) (by omega)
    have id3 : ee n (k + 1) + (2 * n - k) = n + 1 + ee n k := ee_down n k (by omega)
    -- Rewrite exponent terms
    have id1' : q ^ (k + 1 + 1) * q ^ (2 * n - (k + 1)) = q ^ (2 * n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    -- q ^ n * q ^ ee n (k + 2) = q ^ (ee n (k + 1) + k + 2)
    have id2' : q ^ n * q ^ ee n (k + 2) = q ^ (ee n (k + 1) + k + 2) := by
      rw [← pow_add]
      congr 1
      have : ee n (k + 2) = n + 1 + ee n (k + 1) - (2 * n - (k + 1)) := by rw [← id2]; omega
      omega
    -- q ^ (n + 1) * q ^ ee n k = q ^ (ee n (k + 1) + (2 * n - k))
    have id3' : q ^ (n + 1) * q ^ ee n k = q ^ (ee n (k + 1) + (2 * n - k)) := by
      rw [← pow_add, id3]
    -- Compute both sides explicitly
    have lhs_eq : q ^ ee n (k + 1) *
        (q ^ (2 * n - k) * qb q (2 * n) k + qb q (2 * n) (k + 1) +
          q ^ (k + 1 + 1) * (q ^ (2 * n - (k + 1)) * qb q (2 * n) (k + 1) + qb q (2 * n) (k + 1 + 1))) =
        q ^ (ee n (k + 1) + (2 * n - k)) * qb q (2 * n) k +
        q ^ ee n (k + 1) * qb q (2 * n) (k + 1) +
        q ^ (ee n (k + 1) + (2 * n + 1)) * qb q (2 * n) (k + 1) +
        q ^ (ee n (k + 1) + k + 2) * qb q (2 * n) (k + 2) := by
      rw [mul_add, mul_add]
      -- Expand the nested multiplication in the third term
      conv_lhs => right; right; rw [mul_add, ← mul_assoc, id1']
      ring
    have rhs_eq : (1 + q ^ (2 * n + 1)) * (q ^ ee n (k + 1) * qb q (2 * n) (k + 1)) +
        q ^ n * (q ^ ee n (k + 2) * qb q (2 * n) (k + 2)) +
        q ^ (n + 1) * (q ^ ee n k * qb q (2 * n) k) =
        q ^ (ee n (k + 1) + (2 * n - k)) * qb q (2 * n) k +
        q ^ ee n (k + 1) * qb q (2 * n) (k + 1) +
        q ^ (ee n (k + 1) + (2 * n + 1)) * qb q (2 * n) (k + 1) +
        q ^ (ee n (k + 1) + k + 2) * qb q (2 * n) (k + 2) := by
      rw [add_mul, one_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      rw [id2', id3']
      ring
    rw [lhs_eq, rhs_eq]
  · -- Case: k + 1 > 2 * n, so k ≥ 2 * n
    push_neg at hk
    have hk' : 2 * n < k + 1 := hk
    have hqb_k1 : qb q (2 * n) (k + 1) = 0 := qb_eq_zero_of_lt q (by omega)
    have hqb_k2 : qb q (2 * n) (k + 2) = 0 := qb_eq_zero_of_lt q (by omega)
    simp [hqb_k1, hqb_k2]
    -- Now k = 2 * n or k > 2 * n
    by_cases hk'' : k = 2 * n
    · subst hk''
      simp
      -- Need: q ^ ee n (2 * n + 1) = q ^ (n + 1) * q ^ ee n (2 * n)
      -- i.e., ee n (2 * n + 1) = n + 1 + ee n (2 * n)
      have h_ee_down : ee n (2 * n + 1) = n + 1 + ee n (2 * n) := by
        have := ee_down n (2 * n) (by omega : 2 * n ≤ 2 * n)
        simp at this ⊢
        linarith
      rw [h_ee_down]
      ring
    · -- k > 2 * n
      have hk''' : 2 * n < k := by omega
      have hqb_k : qb q (2 * n) k = 0 := qb_eq_zero_of_lt q hk'''
      simp [hqb_k]

/-- Enlarging the summation range does not change the finite Jacobi sum. -/
