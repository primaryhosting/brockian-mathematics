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

lemma qb_mul_qpoch (q : R) {m k : ℕ} (h : k ≤ m) :
    qb q m k * qpoch q k * qpoch q (m - k) = qpoch q m := by
  induction m generalizing k with
  | zero =>
    simp [Nat.le_zero.mp h]
  | succ m ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [qb_succ_succ]
      have hm : m + 1 - (k + 1) = m - k := by omega
      rw [hm, qpoch_succ]
      by_cases hk : k + 1 ≤ m
      · have ihm : k + 1 ≤ m := hk
        have ihm' : k ≤ m := by omega
        have hmk : m - k = m - (k + 1) + 1 := by omega
        have hexp : m - (k + 1) + 1 = m - k := hmk.symm
        -- Rewrite qpoch q (m - k) in terms of qpoch q (m - (k+1))
        have hqpoch_mk : qpoch q (m - k) = qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) := by
          conv_lhs => rw [hmk]
          rw [qpoch_succ, hexp]
        -- Rewrite qpoch q (k + 1) in terms of qpoch q k
        have hk1 : qpoch q (k + 1) = qpoch q k * (1 - q ^ (k + 1)) := qpoch_succ q k
        -- IH instances
        have eq1 : qb q m k * qpoch q k * qpoch q (m - k) = qpoch q m := ih ihm'
        have eq2 : qb q m (k + 1) * qpoch q (k + 1) * qpoch q (m - (k + 1)) = qpoch q m := ih ihm
        rw [hqpoch_mk] at eq1
        rw [hk1] at eq2
        -- Goal after qpoch_succ on RHS
        rw [qpoch_succ q m]
        rw [hqpoch_mk]
        -- Expand the LHS
        have lhs_expand : (qb q m k + q ^ (k + 1) * qb q m (k + 1)) *
            (qpoch q k * (1 - q ^ (k + 1))) * (qpoch q (m - (k + 1)) * (1 - q ^ (m - k))) =
          qb q m k * qpoch q k * (1 - q ^ (k + 1)) * qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) +
          q ^ (k + 1) * qb q m (k + 1) * qpoch q k * (1 - q ^ (k + 1)) *
            qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) := by ring
        rw [lhs_expand]
        -- Use eq1 and eq2 to simplify
        -- eq1: qb q m k * qpoch q k * qpoch q (m - (k+1)) * (1 - q^(m-k)) = qpoch q m
        -- So term1 = eq1 * (1 - q^(k+1)) = qpoch q m * (1 - q^(k+1))
        have term1 : qb q m k * qpoch q k * (1 - q ^ (k + 1)) * qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) =
            qpoch q m * (1 - q ^ (k + 1)) := by
          linear_combination eq1 * (1 - q ^ (k + 1))
        -- eq2: qb q m (k+1) * qpoch q (k+1) * qpoch q (m - (k+1)) = qpoch q m
        -- So term2 = eq2 * q^(k+1) * (1 - q^(m-k)) = qpoch q m * q^(k+1) * (1 - q^(m-k))
        have term2 : q ^ (k + 1) * qb q m (k + 1) * qpoch q k * (1 - q ^ (k + 1)) *
            qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) =
            qpoch q m * q ^ (k + 1) * (1 - q ^ (m - k)) := by
          linear_combination eq2 * q ^ (k + 1) * (1 - q ^ (m - k))
        rw [term1, term2]
        -- LHS = qpoch q m * (1 - q^(k+1)) + qpoch q m * q^(k+1) * (1 - q^(m-k))
        --     = qpoch q m * [(1 - q^(k+1)) + q^(k+1) * (1 - q^(m-k))]
        --     = qpoch q m * [1 - q^(k+1) + q^(k+1) - q^(m+1)]
        --     = qpoch q m * (1 - q^(m+1)) = RHS
        have hexp2 : q ^ (k + 1) * q ^ (m - k) = q ^ (m + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hexp2' : q * q ^ k * q ^ (m - k) = q * q ^ m := by
          simp_rw [mul_assoc, ← pow_add, show k + (m - k) = m by omega]
        linear_combination -hexp2 * qpoch q m
      · have hz : qb q m (k + 1) = 0 := qb_eq_zero_of_lt q (by omega)
        have hmk : k = m := by omega
        have hqbm : qb q m m = 1 := by
          clear h hm hk hz hmk ih
          induction m with
          | zero => rfl
          | succ n ih => rw [qb_succ_succ]; simp [ih, qb_eq_zero_of_lt q (by omega : n < n + 1)]
        have hqbm1 : qb q m (m + 1) = 0 := qb_eq_zero_of_lt q (by omega)
        simp [hmk, hqbm, hqbm1, qpoch_succ]

end QB

/-! ## The finite Jacobi triple product -/

/-- The `m`-th triangular number. -/
