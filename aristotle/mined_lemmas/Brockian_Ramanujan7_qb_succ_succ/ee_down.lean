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

lemma ee_down (n k : ℕ) (h : k ≤ 2 * n) : ee n (k + 1) + (2 * n - k) = n + 1 + ee n k := by
  by_cases hn : n ≤ k
  · -- Case: n ≤ k, so ee n k = tri (k - n)
    have hn1 : n ≤ k + 1 := by omega
    simp [ee, hn, hn1]
    -- Let d = k - n
    set d := k - n with hd_def
    have hd2 : k + 1 - n = d + 1 := by omega
    have hd3 : 2 * n - k = n - d := by omega
    rw [hd2, hd3]
    -- Need: tri (d + 1) + (n - d) = n + 1 + tri d
    -- i.e., tri (d + 1) = tri d + (d + 1)
    have tri_succ : tri (d + 1) = tri d + (d + 1) := by
      simp only [tri]
      have h : (d + 1) * (d + 1 + 1) = d * (d + 1) + 2 * (d + 1) := by ring
      omega
    rw [tri_succ]
    omega
  · -- Case: k < n, so ee n k = tri (n - k - 1)
    push_neg at hn
    simp [ee, hn]
    by_cases hn1 : k + 1 ≥ n
    · -- Subcase: k + 1 ≥ n, which means k + 1 = n since k < n
      have hk1 : k + 1 = n := by omega
      have hk : ¬(n ≤ k) := by omega
      simp [hk]
      simp [tri]
      simp [hk1]
      have : n - k - 1 = 0 := by omega
      simp [this]
      omega
    · -- Subcase: k + 1 < n
      push_neg at hn1
      have hk : ¬(n ≤ k) := by omega
      have hk1 : ¬(n ≤ k + 1) := by omega
      simp [hk, hk1, tri]
      -- Let m = n - k - 1, then n - (k+1) - 1 = m - 1
      set m := n - k - 1 with hm_def
      have hm_pos : m ≥ 1 := by omega
      have h1 : n - (k + 1) - 1 = m - 1 := by omega
      have h2 : 2 * n - k = n + m + 1 := by omega
      rw [h1, h2]
      -- Need: tri (m-1) + (n + m + 1) = n + 1 + tri m
      -- i.e., tri (m-1) + m = tri m
      have tri_add : (m - 1) * m / 2 + m = m * (m + 1) / 2 := by
        have heq : (m - 1) * m + 2 * m = m * (m + 1) := by nlinarith [Nat.sub_add_cancel hm_pos]
        have : ((m - 1) * m + 2 * m) / 2 = ((m - 1) * m) / 2 + m := by
          rw [← Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
        omega
      simp [Nat.sub_add_cancel hm_pos]
      linarith [tri_add]

section FJTP

variable {R : Type*} [CommRing R]

/-- The coefficient of `z ^ k` in the finite Jacobi triple product of order `n`. -/
