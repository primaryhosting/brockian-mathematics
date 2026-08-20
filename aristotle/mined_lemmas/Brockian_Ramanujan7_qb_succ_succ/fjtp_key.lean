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

theorem fjtp_key (q : R) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * ((k : R) - (N : R))) * cc q N k
      = (-1 : R) ^ (N + 1) * (qpoch q N * qpoch q (N - 1)) := by
  have h1 := fjtp_eps q N hN
  have h2 := fjtp_fst q N hN
  have hsplit : ∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * ((k : R) - (N : R))) * cc q N k
      = (∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * (k : R)) * cc q N k)
        + (N : R) * ∑ k ∈ range (2 * N + 1), (-1 : R) ^ k * cc q N k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ]
    ring
  rw [hsplit, h1, h2, mul_zero, add_zero]

/-- Splitting a sum over `range (2 * N + 1)` at the midpoint `k = N`. -/
