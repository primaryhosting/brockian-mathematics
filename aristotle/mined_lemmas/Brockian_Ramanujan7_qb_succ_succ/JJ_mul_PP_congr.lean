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

lemma JJ_mul_PP_congr (d : ℕ) : (X : S7) ^ (d + 1) ∣ (JJ * PP - EE ^ 2) := by
  have hJ : (X : S7) ^ (d + 1) ∣ (Jpart (2 * d + 2) - JJ) :=
    Jpart_congr d (2 * d + 2) (by have := self_le_tri (2 * d + 2); omega)
  have h1 : (X : S7) ^ (d + 1) ∣ (JJ * PP - Jpart (2 * d + 2) * PP) := by
    have h2 := hJ.mul_right PP
    have h3 : (Jpart (2 * d + 2) - JJ) * PP = -(JJ * PP - Jpart (2 * d + 2) * PP) := by ring
    rw [h3, dvd_neg] at h2
    exact h2
  have h4 := dvd_add h1 (key_congr d)
  have h5 : (JJ * PP - Jpart (2 * d + 2) * PP) + (Jpart (2 * d + 2) * PP - EE ^ 2)
      = JJ * PP - EE ^ 2 := by ring
  rwa [h5] at h4

