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

lemma qb_step (q : R) (m k : ℕ) :
    qb q (m + 2) (k + 2)
      = (1 + q ^ (m + 1)) * qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2)
        + q ^ (m - k) * qb q m k := by
  rw [qb_succ_succ, qb_pascal2, qb_pascal2]
  by_cases hkm : k + 1 ≤ m
  · have hexp : k + 2 + (m - (k + 1)) = m + 1 := by
      have h1 : m - (k + 1) = m - k - 1 := by omega
      rw [h1]
      omega
    have hpow : q ^ (k + 2) * q ^ (m - (k + 1)) = q ^ (m + 1) := by
      rw [← pow_add]
      congr 1
    calc q ^ (m - k) * qb q m k + qb q m (k + 1) +
        q ^ (k + 2) * (q ^ (m - (k + 1)) * qb q m (k + 1) + qb q m (k + 2))
      _ = q ^ (m - k) * qb q m k + qb q m (k + 1) +
          q ^ (k + 2) * q ^ (m - (k + 1)) * qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2) := by ring
      _ = q ^ (m - k) * qb q m k + qb q m (k + 1) + q ^ (m + 1) * qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2) := by rw [hpow]
      _ = (1 + q ^ (m + 1)) * qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2) + q ^ (m - k) * qb q m k := by ring
  · have hq : qb q m (k + 1) = 0 := qb_eq_zero_of_lt q (by omega)
    simp [hq]
    ring

/-- The `q`-Pochhammer symbol `(q; q)_n = ∏_{i=1}^{n} (1 - q^i)`. -/
