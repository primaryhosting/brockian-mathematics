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

lemma cc_gen_step (q z : R) (n : ℕ) :
    ∑ k ∈ range (2 * (n + 1) + 1), cc q (n + 1) k * z ^ k
      = (∑ k ∈ range (2 * n + 1), cc q n k * z ^ k)
          * (q ^ n + (1 + q ^ (2 * n + 1)) * z + q ^ (n + 1) * z ^ 2) := by
  have hrange : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
  rw [hrange, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  have hterm : ∀ k ∈ range (2 * n + 1), cc q (n + 1) (k + 1 + 1) * z ^ (k + 1 + 1)
      = (1 + q ^ (2 * n + 1)) * (cc q n (k + 1) * z ^ (k + 2))
        + q ^ n * (cc q n (k + 2) * z ^ (k + 2)) + q ^ (n + 1) * (cc q n k * z ^ (k + 2)) := by
    intro k _
    rw [show k + 1 + 1 = k + 2 from rfl, cc_rec2]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, cc_shiftA, cc_shiftB, cc_shiftC,
    cc_rec1, cc_rec0]
  ring

/-- The finite form of the Jacobi triple product. -/
