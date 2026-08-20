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

lemma key_sumB_congr (d N : ℕ) (hN : 2 * d + 2 ≤ N) :
    (X : S7) ^ (d + 1) ∣
      (∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1))
          * (X ^ tri j * qb (X : S7) (2 * N) (N - 1 - j))
        - ∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1)) * (X ^ tri j * PP)) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j hj => ?_
  rw [Finset.mem_range] at hj
  by_cases hcase : j ≤ N - 1 - d
  · exact term_dvd_of_dvd _ _ _ _ _
      (qb_congr d (2 * N) (N - 1 - j) (by omega) (by omega) (by omega))
  · refine term_dvd_of_high _ _ ?_ _ _ _
    have := self_le_tri j
    omega

/-- The two `PP`-sums combine into `- Jpart N * PP`, up to a term of high order. -/
