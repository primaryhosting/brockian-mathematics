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

lemma cc_shiftA (q z : R) (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), cc q n (k + 2) * z ^ (k + 2)
      = (∑ k ∈ range (2 * n + 1), cc q n k * z ^ k) - cc q n 0 - cc q n 1 * z := by
  have h3 : ∑ k ∈ range (2 * n + 3), cc q n k * z ^ k
      = ∑ k ∈ range (2 * n + 1), cc q n k * z ^ k := sum_cc_ext q z n (2 * n + 3) (by omega)
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from rfl, Finset.sum_range_succ',
    show 2 * n + 2 = (2 * n + 1) + 1 from rfl, Finset.sum_range_succ'] at h3
  simp only [pow_zero, mul_one] at h3
  rw [← h3]
  ring

/-- Shifting the index of the finite Jacobi sum by one. -/
