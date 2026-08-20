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

lemma qb_pascal2 (q : R) (n k : ℕ) :
    qb q (n + 1) (k + 1) = q ^ (n - k) * qb q n k + qb q n (k + 1) := by
  -- First prove the ratio property: qb q m (k + 1) * (1 - q ^ (k + 1)) = qb q m k * (1 - q ^ (m - k))
  have qb_ratio : ∀ m k, k ≤ m → qb q m (k + 1) * (1 - q ^ (k + 1)) = qb q m k * (1 - q ^ (m - k)) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      simp at hk
      simp [qb]
    | succ m ihm =>
      intro k hk
      cases k with
      | zero =>
        -- Need: qb q (m + 1) 1 * (1 - q) = qb q (m + 1) 0 * (1 - q ^ (m + 1))
        -- qb q (m + 1) 0 = 1
        -- qb q (m + 1) 1 = ∑ i ∈ range (m + 1), q ^ i
        simp only [qb_zero_right]
        -- First prove qb q (m + 1) 1 = ∑ i ∈ range (m + 1), q ^ i
        have qb1 : qb q (m + 1) 1 = ∑ i ∈ range (m + 1), q ^ i := by
          have : ∀ n, qb q n 1 = ∑ i ∈ range n, q ^ i := by
            intro n
            induction n with
            | zero => simp [qb]
            | succ n ih =>
              simp [qb_succ_succ, ih, Finset.range_add_one]
              linear_combination geom_sum_mul q n
          exact this (m + 1)
        rw [qb1]
        have h := geom_sum_mul q (m + 1)
        simp
        -- h: (∑ i ∈ range (m + 1), q ^ i) * (q - 1) = q ^ (m + 1) - 1
        -- Need: (∑ i ∈ range (m + 1), q ^ i) * (1 - q) = 1 - q ^ (m + 1)
        linear_combination -h
      | succ k =>
        -- Goal: qb q (m + 1) (k + 2) * (1 - q ^ (k + 2)) = qb q (m + 1) (k + 1) * (1 - q ^ (m - k))
        have hkm' : k ≤ m := by omega
        -- Handle two cases: k < m and k = m
        by_cases hkm : k < m
        · -- k < m, so k + 1 ≤ m, can use IH for both k and k + 1
          have ih1 := ihm k hkm'  -- qb q m (k + 1) * (1 - q^(k+1)) = qb q m k * (1 - q^(m-k))
          have ih2 := ihm (k + 1) (by omega)  -- qb q m (k + 2) * (1 - q^(k+2)) = qb q m (k + 1) * (1 - q^(m-k-1))
          have ih2' : qb q m (k + 2) * (1 - q ^ (k + 2)) = qb q m (k + 1) * (1 - q ^ (m - (k + 1))) := by omega;
          simp only [qb_succ_succ]
          have hmk'' : m + 1 - (k + 1) = m - k := by omega
          rw [hmk'']
          calc (qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2)) * (1 - q ^ (k + 2))
              = qb q m (k + 1) * (1 - q ^ (k + 2)) + q ^ (k + 2) * qb q m (k + 2) * (1 - q ^ (k + 2)) := by ring
            _ = qb q m (k + 1) * (1 - q ^ (k + 2)) + q ^ (k + 2) * (qb q m (k + 1) * (1 - q ^ (m - (k + 1)))) := by linear_combination q ^ (k + 2) * ih2'
            _ = qb q m (k + 1) * ((1 - q ^ (k + 2)) + q ^ (k + 2) * (1 - q ^ (m - (k + 1)))) := by ring
            _ = qb q m (k + 1) * (1 - q ^ (m + 1)) := by
                congr 1
                have hexp : 2 + k + (m - (1 + k)) = m + 1 := by omega
                have h1 : q ^ 2 * q ^ k * q ^ (m - (1 + k)) = q ^ (m + 1) := by
                  rw [← pow_add, ← pow_add, hexp]
                ring_nf
                rw [h1]
                ring
            _ = (qb q m k + q ^ (k + 1) * qb q m (k + 1)) * (1 - q ^ (m - k)) := by
                calc qb q m (k + 1) * (1 - q ^ (m + 1))
                    = qb q m (k + 1) * (1 - q ^ (k + 1)) + qb q m (k + 1) * (q ^ (k + 1) - q ^ (m + 1)) := by ring
                  _ = qb q m (k + 1) * (1 - q ^ (k + 1)) + qb q m (k + 1) * q ^ (k + 1) * (1 - q ^ (m - k)) := by
                    congr 1
                    have hexp : k + 1 + (m - k) = m + 1 := by omega
                    have heq : q ^ (k + 1) * q ^ (m - k) = q ^ (m + 1) := by rw [← pow_add, hexp]
                    linear_combination qb q m (k + 1) * heq
                  _ = qb q m k * (1 - q ^ (m - k)) + qb q m (k + 1) * q ^ (k + 1) * (1 - q ^ (m - k)) := by rw [ih1]
                  _ = (qb q m k + q ^ (k + 1) * qb q m (k + 1)) * (1 - q ^ (m - k)) := by ring
        · -- k = m
          have hk_eq_m : k = m := by omega
          subst hk_eq_m
          norm_num
          -- qb q (k + 1) (k + 2) = 0 since k + 2 > k + 1
          have hqb : qb q (k + 1) (k + 2) = 0 := qb_eq_zero_of_lt q (by omega)
          rw [hqb]
          ring
  have key : ∀ m k, qb q m k + q ^ (k + 1) * qb q m (k + 1) = q ^ (m - k) * qb q m k + qb q m (k + 1) := by
    intro m k
    by_cases h : k ≤ m
    · have := qb_ratio m k h
      calc qb q m k + q ^ (k + 1) * qb q m (k + 1)
          = qb q m k * 1 + q ^ (k + 1) * qb q m (k + 1) * 1 := by ring
        _ = qb q m k * (1 - q ^ (m - k)) + qb q m k * q ^ (m - k) + q ^ (k + 1) * qb q m (k + 1) := by ring
        _ = qb q m (k + 1) * (1 - q ^ (k + 1)) + qb q m k * q ^ (m - k) + q ^ (k + 1) * qb q m (k + 1) := by rw [this]
        _ = qb q m (k + 1) + qb q m k * q ^ (m - k) := by ring
        _ = q ^ (m - k) * qb q m k + qb q m (k + 1) := by ring
    · push_neg at h
      have h1 : qb q m k = 0 := qb_eq_zero_of_lt q h
      have h2 : qb q m (k + 1) = 0 := qb_eq_zero_of_lt q (by omega)
      simp [h1, h2]
  rw [qb_succ_succ, key]

/-- The ratio identity between consecutive Gaussian binomial coefficients. -/
