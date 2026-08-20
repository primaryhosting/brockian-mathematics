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

lemma key_congr (d : ℕ) : (X : S7) ^ (d + 1) ∣ (Jpart (2 * d + 2) * PP - EE ^ 2) := by
  -- Use N = 2*d + 2, which satisfies 2*d + 2 ≤ N trivially
  set N := 2 * d + 2 with hN_def
  -- N is even
  have heven : Even N := ⟨d + 1, by omega⟩
  -- We need high-order congruences; 2*d + 2 ≤ N is trivially true
  have hND : 2 * d + 2 ≤ N := le_refl _
  have hA := key_sumA_congr d N hND
  have hB := key_sumB_congr d N hND
  -- Combine hA and hB: the qb-sums are close to the PP-sums
  have hAB : (X : S7) ^ (d + 1) ∣
      (∑ j ∈ range (N + 1), ((-1 : S7) ^ (j + 1) * (j : S7)) * (X ^ tri j * qb (X : S7) (2 * N) (N + j))
        + ∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1)) * (X ^ tri j * qb (X : S7) (2 * N) (N - 1 - j)))
      - (∑ j ∈ range (N + 1), ((-1 : S7) ^ (j + 1) * (j : S7)) * (X ^ tri j * PP)
        + ∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1)) * (X ^ tri j * PP)) := by
    convert dvd_add hA hB using 1; ring
  -- Use key_split to express qb-sums in terms of cc
  have hsplit := key_split (X : S7) N heven
  -- Use key_sums_eq to simplify PP-sums
  have hsums := key_sums_eq N
  -- Use fjtp_key to express the cc-sum
  have hNpos : 0 < N := by omega
  have hfjtp := fjtp_key (X : S7) N hNpos
  -- Rewrite hAB using hsplit and hfjtp
  rw [← hsplit, hfjtp] at hAB
  -- Rewrite hAB using hsums
  rw [hsums] at hAB
  -- hAB : X^(d+1) ∣ (-1)^(N+1) * qpoch * qpoch - (-Jpart N + term) * PP
  --      = (-1)^(N+1) * qpoch * qpoch + Jpart N * PP - term * PP
  have hAB' : (X : S7) ^ (d + 1) ∣
      Jpart N * PP + ((-1 : S7) ^ (N + 1)) * (qpoch (X : S7) N * qpoch (X : S7) (N - 1))
      - ((-1 : S7) ^ (N + 1)) * (N : S7) * X ^ tri N * PP := by
    convert hAB using 1; ring
  -- N = 2*d + 2 is even, so (-1)^(N+1) = -1
  have hN_even : Even N := heven
  have hNp1_odd : Odd (N + 1) := hN_even.add_odd (by decide : Odd 1)
  have hsign : ((-1 : S7) ^ (N + 1)) = -1 := by
    rw [neg_one_pow_eq_pow_mod_two]; simp [Nat.odd_iff.mp hNp1_odd]
  rw [hsign] at hAB'
  -- hAB' : X^(d+1) ∣ Jpart N * PP + (-1) * qpoch * qpoch - (-1) * N * X^tri N * PP
  --       = Jpart N * PP - qpoch * qpoch + N * X^tri N * PP
  have hAB'' : (X : S7) ^ (d + 1) ∣ Jpart N * PP - qpoch (X : S7) N * qpoch (X : S7) (N - 1)
      + (N : S7) * X ^ tri N * PP := by convert hAB' using 1; ring
  -- tri N = N*(N+1)/2 = (2*d+2)*(2*d+3)/2 = (d+1)*(2*d+3) ≥ d+1
  have htri : tri N ≥ d + 1 := by
    simp only [tri]
    rw [hN_def]
    have h1 : (2 * d + 2) * (2 * d + 2 + 1) = 2 * (d + 1) * (2 * d + 3) := by ring
    have h2 : 2 * (d + 1) * (2 * d + 3) / 2 = (d + 1) * (2 * d + 3) := by
      rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [h1, h2]
    have : (d + 1) * (2 * d + 3) ≥ d + 1 := Nat.le_mul_of_pos_right _ (by omega)
    exact this
  -- N * X^tri N * PP is divisible by X^(d+1)
  have hterm : (X : S7) ^ (d + 1) ∣ (N : S7) * X ^ tri N * PP := by
    have : (X : S7) ^ (d + 1) ∣ X ^ tri N := pow_dvd_pow _ htri
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this (N : S7)) PP
  -- qpoch N * qpoch (N-1) ≈ EE^2 (mod X^(d+1))
  have hN_ge_d : d ≤ N := by omega
  have hN1_ge_d : d ≤ N - 1 := by omega
  have hEE_N := EE_congr d N hN_ge_d
  have hEE_N1 := EE_congr d (N - 1) hN1_ge_d
  -- qpoch N * qpoch (N-1) - EE^2 = qpoch N * (qpoch (N-1) - EE) + EE * (qpoch N - EE)
  have hEE_sq : (X : S7) ^ (d + 1) ∣ qpoch (X : S7) N * qpoch (X : S7) (N - 1) - EE ^ 2 := by
    have h1 : qpoch (X : S7) N * qpoch (X : S7) (N - 1) - EE ^ 2 =
        qpoch (X : S7) N * (qpoch (X : S7) (N - 1) - EE) + EE * (qpoch (X : S7) N - EE) := by ring
    rw [h1]
    exact dvd_add (dvd_mul_of_dvd_right hEE_N1 _) (dvd_mul_of_dvd_right hEE_N _)
  -- Combine: (Jpart N * PP - qpoch N * qpoch (N-1)) = (divisible) - term
  have h1 : (X : S7) ^ (d + 1) ∣ Jpart N * PP - qpoch (X : S7) N * qpoch (X : S7) (N - 1) := by
    have := dvd_sub hAB'' hterm
    convert this using 1; ring
  -- Now: Jpart N * PP - EE^2 = (Jpart N * PP - qpoch N * qpoch (N-1)) + (qpoch N * qpoch (N-1) - EE^2)
  have h2 : (X : S7) ^ (d + 1) ∣ Jpart N * PP - EE ^ 2 := by
    have := dvd_add h1 hEE_sq
    convert this using 1; ring
  exact h2

