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

lemma qb_congr (d m k : ℕ) (hk : d ≤ k) (hkm : k ≤ m) (hmk : d ≤ m - k) :
    (X : S7) ^ (d + 1) ∣ (qb (X : S7) m k - PP) := by
  set B := qb (X : S7) m k with hB
  have hprod := qb_mul_qpoch (X : S7) hkm
  have h1 : (X : S7) ^ (d + 1) ∣ (qpoch (X : S7) k - EE) := EE_congr d k hk
  have h2 : (X : S7) ^ (d + 1) ∣ (qpoch (X : S7) (m - k) - EE) := EE_congr d (m - k) hmk
  have h3 : (X : S7) ^ (d + 1) ∣ (qpoch (X : S7) m - EE) := EE_congr d m (hk.trans hkm)
  have e0 : (X : S7) ^ (d + 1) ∣ (B - B) := by simp
  have h4 : (X : S7) ^ (d + 1) ∣ (B * qpoch (X : S7) k * qpoch (X : S7) (m - k) - B * EE * EE) :=
    dvd_sub_mul (dvd_sub_mul e0 h1) h2
  rw [hprod] at h4
  have h5 : (X : S7) ^ (d + 1) ∣ (B * EE * EE - EE) := by
    have hd := dvd_sub h3 h4
    have heq : (qpoch (X : S7) m - EE) - (qpoch (X : S7) m - B * EE * EE) = B * EE * EE - EE := by
      ring
    rwa [heq] at hd
  have hEE : PP * EE * EE = EE := by rw [PP_mul_EE, one_mul]
  have h6 : (X : S7) ^ (d + 1) ∣ (B * EE * EE - PP * EE * EE) := by rw [hEE]; exact h5
  exact dvd_of_dvd_mul_EE (dvd_of_dvd_mul_EE h6)

/-- Partial sums of the Jacobi series approximate `JJ`. -/
