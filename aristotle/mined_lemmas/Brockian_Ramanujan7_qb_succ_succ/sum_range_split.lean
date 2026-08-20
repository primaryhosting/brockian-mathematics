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

lemma sum_range_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ range (2 * N + 1), f k
      = ∑ j ∈ range (N + 1), f (N + j) + ∑ j ∈ range N, f (N - 1 - j) := by
  have h2N1 : 2 * N + 1 = N + (N + 1) := by ring
  rw [h2N1]
  rw [← sum_range_add_sum_Ico _ (by omega : N ≤ N + (N + 1))]
  simp_rw [sum_Ico_eq_sum_range]
  have hsimp : N + (N + 1) - N = N + 1 := by omega
  rw [hsimp]
  rw [add_comm]
  congr 1
  exact (@Finset.sum_range_reflect _ _ f N).symm

/-- Splitting the key sum at `k = N` (for even `N`). -/
