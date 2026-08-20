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

lemma factor_mul_eq_one (i : ℕ) :
    (1 - (X : S7) ^ (i + 1)) * (1 + ∑' j : ℕ, (1 : ZMod 7) • (X : S7) ^ ((i + 1) * (j + 1)))
      = 1 := by
  have hc : PowerSeries.constantCoeff ((X : S7) ^ (i + 1)) = 0 := by simp
  have hsum : Summable (fun j : ℕ => ((X : S7) ^ (i + 1)) ^ j) :=
    PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hc
  have key : (1 + ∑' j : ℕ, (1 : ZMod 7) • (X : S7) ^ ((i + 1) * (j + 1)))
      = ∑' j : ℕ, ((X : S7) ^ (i + 1)) ^ j := by
    rw [hsum.tsum_eq_zero_add]
    simp [pow_succ, pow_mul, mul_comm]
  rw [key]
  exact PowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero hc

