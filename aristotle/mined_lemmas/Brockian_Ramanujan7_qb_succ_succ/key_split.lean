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

theorem key_split (q : R) (N : ℕ) (hN : Even N) :
    ∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * ((k : R) - (N : R))) * cc q N k
      = ∑ j ∈ range (N + 1), ((-1 : R) ^ (j + 1) * (j : R)) * (q ^ tri j * qb q (2 * N) (N + j))
        + ∑ j ∈ range N, ((-1 : R) ^ (j + 1) * ((j : R) + 1))
            * (q ^ tri j * qb q (2 * N) (N - 1 - j)) := by
  rw [sum_range_split]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hN_even : (-1 : R) ^ N = 1 := by rw [hN.neg_one_pow]
    have hpow : (-1 : R) ^ (N + j + 1) = (-1 : R) ^ (j + 1) := by
      rw [pow_add, pow_add, hN_even]; ring
    rw [cc, ee_add, hpow]
    simp [Nat.cast_add]
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < N := by simp at hj; exact hj
    have hN_even : (-1 : R) ^ N = 1 := by rw [hN.neg_one_pow]
    rw [cc, ee_sub _ _ hj']
    -- Need to show (-1)^(N - j) = (-1)^j when N is even
    have hN_ge_j : N ≥ j := le_of_lt hj'
    have hpow : (-1 : R) ^ (N - 1 - j + 1) = (-1 : R) ^ j := by
      have heq : N - 1 - j + 1 = N - j := by omega
      rw [heq]
      by_cases hj_even : Even j
      · have hNj_even : Even (N - j) := by rw [Nat.even_sub hN_ge_j]; simp [hN, hj_even]
        rw [hj_even.neg_one_pow, hNj_even.neg_one_pow]
      · have hj_odd : Odd j := by simpa using hj_even
        have hNj_odd : Odd (N - j) := by
          obtain ⟨m, hm⟩ := hj_odd
          obtain ⟨n, hn⟩ := hN
          subst hm hn
          use n - m - 1
          omega
        rw [hj_odd.neg_one_pow, hNj_odd.neg_one_pow]
    rw [hpow]
    have hsub : ((N - 1 - j : ℕ) : R) - N = -((j : R) + 1) := by
      have h1 : N ≥ 1 + j := by omega
      rw [Nat.sub_sub, Nat.cast_sub h1]
      simp
      ring
    simp [hsub]
    ring

end FJTP

/-! ## Power series over `ZMod 7` -/

/-- Power series over `ZMod 7`. -/
abbrev S7 : Type := PowerSeries (ZMod 7)

section PS

local instance : TopologicalSpace (ZMod 7) := ⊥
local instance : DiscreteTopology (ZMod 7) := ⟨rfl⟩

/-! ### Congruences modulo `X ^ (d+1)` -/

