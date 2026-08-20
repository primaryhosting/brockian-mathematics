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

lemma coeff_PP_step (n : ℕ) (ih : ∀ t < n, (coeff (7 * t + 5)) PP = 0) :
    (coeff (7 * n + 5)) PP = 0 := by
  -- From PP * EE^7 = JJ^2, coeff (7*n+5) PP * EE^7 = coeff (7*n+5) JJ^2 = 0
  have heq : coeff (7 * n + 5) (PP * EE ^ 7) = coeff (7 * n + 5) (JJ ^ 2) := by
    rw [PP_mul_EE_pow_seven]
  have hzero : coeff (7 * n + 5) (JJ ^ 2) = 0 := coeff_JJ_sq _ (by omega : (7 * n + 5) % 7 = 5)
  rw [hzero] at heq
  -- Expand coeff (PP * EE^7) as a sum
  rw [PowerSeries.coeff_mul] at heq
  -- The sum only has terms where the second component is divisible by 7
  -- Since p.1 + p.2 = 7*n + 5, if 7 ∣ p.2 then p.1 ≡ 5 (mod 7)
  -- By IH, coeff p.1 PP = 0 unless p.1 = 7*n + 5 (i.e., p.2 = 0)
  rw [Finset.sum_eq_single (7 * n + 5, 0)] at heq
  · change coeff (7 * n + 5) PP * coeff 0 (EE ^ 7) = 0 at heq
    rw [constantCoeff_EE_pow_seven, mul_one] at heq
    exact heq
  · intro p hp hne
    -- p.1 + p.2 = 7*n + 5
    have hsum : p.1 + p.2 = 7 * n + 5 := Finset.mem_antidiagonal.mp hp
    by_cases hdiv : 7 ∣ p.2
    · -- If 7 ∣ p.2, then p.1 = 7*n + 5 - p.2 = 7*(n - k) + 5 for some k > 0
      obtain ⟨k, hk⟩ := hdiv
      have hkpos : 0 < k := by
        by_contra hkneg
        push_neg at hkneg
        have : p = (7 * n + 5, 0) := by
          ext <;> omega
        exact hne this
      have h1 : p.1 = 7 * (n - k) + 5 := by omega
      have hklt : n - k < n := by omega
      rw [h1, ih _ hklt, zero_mul]
    · -- If ¬ 7 ∣ p.2, then coeff p.2 (EE^7) = 0
      rw [mul_eq_zero]
      right
      exact coeff_EE_pow_seven _ hdiv
  · intro h
    exact absurd (h (by simp [Finset.mem_antidiagonal])) (by simp)

