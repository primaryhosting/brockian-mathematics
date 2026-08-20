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

theorem fjtp_fst (q : R) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range (2 * N + 1), (-1 : R) ^ k * cc q N k = 0 := by
  have := finite_jtp q (-1) N
  have hprod : ∏ i ∈ range N, (-(1 : R) + q ^ i) = 0 := by
    rw [Finset.prod_eq_zero (mem_range.mpr hN)]
    simp
  simp_all [mul_comm]

open TrivSqZeroExt DualNumber in
