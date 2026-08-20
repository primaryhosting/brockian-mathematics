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

lemma ee_up (n k : ℕ) : ee n k + n = ee (n + 1) k + k := by
  by_cases h : n ≤ k
  · by_cases h2 : n < k
    · -- n < k: ee n k = tri (k - n), ee (n+1) k = tri (k - n - 1)
      simp [ee, h, show n + 1 ≤ k from Nat.succ_le_of_lt h2]
      have : k - n = k - (n + 1) + 1 := by omega
      rw [this, tri_succ]
      omega
    · -- n = k
      push_neg at h2
      simp [ee, show n = k from le_antisymm h h2]
  · -- n > k
    push_neg at h
    simp [ee]
    split_ifs with h1 h2 <;> try omega
    -- Goal: tri (n - k - 1) + n = tri (n + 1 - k - 1) + k
    -- First simplify n + 1 - k - 1 = n - k
    have heq1 : n + 1 - k - 1 = n - k := by omega
    rw [heq1]
    -- Goal: tri (n - k - 1) + n = tri (n - k) + k
    -- Now use tri_succ: tri (n - k) = tri (n - k - 1) + (n - k)
    have heq2 : n - k = n - k - 1 + 1 := by omega
    rw [heq2, tri_succ]
    simp only [show n - k - 1 + 1 - 1 = n - k - 1 from by omega]
    omega

