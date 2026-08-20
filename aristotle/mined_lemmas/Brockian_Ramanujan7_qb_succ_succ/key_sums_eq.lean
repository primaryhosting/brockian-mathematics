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

lemma key_sums_eq (N : ℕ) :
    (∑ j ∈ range (N + 1), ((-1 : S7) ^ (j + 1) * (j : S7)) * (X ^ tri j * PP)
      + ∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1)) * (X ^ tri j * PP))
      = (- Jpart N + ((-1 : S7) ^ (N + 1) * (N : S7)) * X ^ tri N) * PP := by
  simp only [Jpart, Finset.sum_range_succ]
  -- Rearrange and combine sums
  rw [add_comm, ← add_assoc]
  rw [← Finset.sum_add_distrib]
  -- Simplify each term in the sum
  have hterm : ∀ x ∈ range N, ((-1 : S7) ^ (x + 1) * ((x : S7) + 1) * (X ^ tri x * PP) +
      (-1 : S7) ^ (x + 1) * (x : S7) * (X ^ tri x * PP)) =
      -(C ((-1 : ZMod 7) ^ x * (2 * (x : ZMod 7) + 1)) * X ^ tri x * PP) := by
    intro x _
    noncomm_ring
    simp [mul_assoc, mul_comm, mul_left_comm]
    abel_nf
    simp [mul_add]
    simp [show (2 : S7) = C (2 : ZMod 7) by rfl, mul_comm (C (2 : ZMod 7))]
    have h1 : (-1 : S7) ^ x = C ((-1 : ZMod 7) ^ x) := by simp [map_pow]
    rw [h1]
    simp [mul_comm, mul_left_comm]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_neg_distrib]
  conv_lhs => rw [← Finset.sum_mul]
  ring

/-- The heart of the limiting argument. -/
