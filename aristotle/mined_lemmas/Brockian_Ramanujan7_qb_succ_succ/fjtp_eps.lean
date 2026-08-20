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

theorem fjtp_eps (q : R) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * (k : R)) * cc q N k
      = (-1 : R) ^ (N + 1) * (qpoch q N * qpoch q (N - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := finite_jtp (inl q : DualNumber R) ((-1 : DualNumber R) + ε) (M + 1)
  rw [dual_prodB_eq] at h
  have hsnd := congrArg TrivSqZeroExt.snd h
  rw [dual_snd_sum] at hsnd
  rw [← hsnd, ← mul_assoc, mul_eps_eq, snd_mul_eps, fst_mul, dual_prodA_fst]
  simp
  ring

/-- The key finite identity: the finite form of Jacobi's identity. -/
