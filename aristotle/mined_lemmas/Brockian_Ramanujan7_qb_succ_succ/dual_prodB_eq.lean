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

lemma dual_prodB_eq (q : R) (M : ℕ) :
    ∏ i ∈ range (M + 1), (((-1 : DualNumber R) + ε) + (inl q : DualNumber R) ^ i)
      = inl ((-1 : R) ^ M * qpoch q M) * ε := by
  induction M with
  | zero => simp [qpoch_zero]
  | succ M ih =>
    rw [Finset.prod_range_succ, ih]
    simp [inl_pow, add_comm, add_assoc]
    rw [mul_assoc, eps_mul_eq, inl_mul_inl]
    simp [qpoch_succ, pow_succ]
    ring

open TrivSqZeroExt DualNumber in
/-- The `ε`-component (the derivative at `z = -1`) of `finite_jtp`. -/
