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

lemma Supp7.mul {f g : S7} (hf : Supp7 f) (hg : Supp7 g) : Supp7 (f * g) := by
  intro m hm
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  have hp' : p.1 + p.2 = m := hp
  have : ¬(7 ∣ p.1) ∨ ¬(7 ∣ p.2) := by
    by_contra h
    push_neg at h
    apply hm
    exact ⟨h.1.choose + h.2.choose, by linarith [h.1.choose_spec, h.2.choose_spec]⟩
  cases this with
  | inl hi => simp [hf p.1 hi]
  | inr hj => simp [hg p.2 hj]

