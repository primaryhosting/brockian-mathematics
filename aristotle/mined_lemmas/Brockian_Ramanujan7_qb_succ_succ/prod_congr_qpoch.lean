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

lemma prod_congr_qpoch (d : ℕ) (s : Finset ℕ) (hs : range d ⊆ s) :
    (X : S7) ^ (d + 1) ∣ ((∏ i ∈ s, (1 - (X : S7) ^ (i + 1))) - qpoch (X : S7) d) := by
  have heq : ∏ i ∈ s, (1 - (X : S7) ^ (i + 1)) = qpoch (X : S7) d * ∏ i ∈ s \ range d, (1 - (X : S7) ^ (i + 1)) := by
    rw [← Finset.prod_sdiff hs]
    simp [qpoch, mul_comm]
  rw [heq]
  have h2 : qpoch (X : S7) d * ∏ i ∈ s \ range d, (1 - (X : S7) ^ (i + 1)) - qpoch (X : S7) d =
            qpoch (X : S7) d * (∏ i ∈ s \ range d, (1 - (X : S7) ^ (i + 1)) - 1) := by ring
  rw [h2]
  have h3 : X ^ (d + 1) ∣ (∏ i ∈ s \ range d, (1 - (X : S7) ^ (i + 1))) - 1 := by
    apply prod_factors_congr_one d _ (fun i hi => Nat.le_of_not_lt fun h => Finset.mem_sdiff.mp hi |>.2 (Finset.mem_range.mpr h))
  exact dvd_mul_of_dvd_right h3 _

