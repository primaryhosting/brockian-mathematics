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

lemma PP_mul_EE : PP * EE = 1 := by
  have h2 : HasProd (fun i : ℕ =>
      (1 + ∑' j : ℕ, (1 : ZMod 7) • (X : S7) ^ ((i + 1) * (j + 1))) * (1 - (X : S7) ^ (i + 1)))
      (PP * EE) := hasProd_PP.mul hasProd_EE
  have h3 : (fun i : ℕ =>
      (1 + ∑' j : ℕ, (1 : ZMod 7) • (X : S7) ^ ((i + 1) * (j + 1))) * (1 - (X : S7) ^ (i + 1)))
      = fun _ : ℕ => (1 : S7) := by
    funext i
    rw [mul_comm]
    exact factor_mul_eq_one i
  rw [h3] at h2
  exact h2.unique hasProd_one

/-- A product of factors of high order is congruent to `1`. -/
