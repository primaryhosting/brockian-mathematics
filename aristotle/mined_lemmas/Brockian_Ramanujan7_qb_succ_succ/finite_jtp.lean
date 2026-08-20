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

theorem finite_jtp (q z : R) (n : ℕ) :
    (∏ i ∈ range n, (1 + z * q ^ (i + 1))) * (∏ i ∈ range n, (z + q ^ i))
      = ∑ k ∈ range (2 * n + 1), cc q n k * z ^ k := by
  induction n with
  | zero => simp [cc, ee, tri]
  | succ n ih =>
    rw [Finset.range_add_one, prod_insert (by simp), Finset.range_add_one,
      prod_insert (by simp)]
    have factored : ((1 + z * q ^ (n + 1)) * ∏ i ∈ range n, (1 + z * q ^ (i + 1))) *
        ((z + q ^ n) * ∏ i ∈ range n, (z + q ^ i)) =
        ((∏ i ∈ range n, (1 + z * q ^ (i + 1))) * ∏ i ∈ range n, (z + q ^ i)) *
        ((1 + z * q ^ (n + 1)) * (z + q ^ n)) := by ring
    rw [factored, ih]
    have quad_eq : (1 + z * q ^ (n + 1)) * (z + q ^ n) = q ^ n + (1 + q ^ (2 * n + 1)) * z + q ^ (n + 1) * z ^ 2 := by ring
    rw [quad_eq]
    rw [Finset.range_add_one]
    rw [show insert (2 * n) (range (2 * n)) = range (2 * n + 1) by rw [Finset.range_add_one]]
    rw [← cc_gen_step]
    rw [Finset.range_add_one]

/-! ### Dual numbers: extracting the derivative at `z = -1` -/

open TrivSqZeroExt DualNumber in
