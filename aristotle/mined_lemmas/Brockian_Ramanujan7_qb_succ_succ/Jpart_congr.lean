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

lemma Jpart_congr (d n : ℕ) (h : d < tri n) : (X : S7) ^ (d + 1) ∣ (Jpart n - JJ) := by
  rw [dvd_iff_coeff]
  intro m hm
  simp only [JJ, PowerSeries.coeff_mk]
  -- We need to show coeff m (Jpart n) = jcoef m
  -- jcoef m = ∑ j ∈ range (m+1), if tri j = m then (-1)^j * (2*j+1) else 0
  rw [jcoef, Jpart]
  simp
  -- coeff m (a * X ^ k) = coeff (m - k) a when m >= k, else 0
  -- Let's prove the coefficient simplification
  have coeff_term : ∀ x m : ℕ, (coeff m) (C ((-1 : ZMod 7) ^ x * (2 * x + 1)) * X ^ tri x) =
      if m = tri x then (-1 : ZMod 7) ^ x * (2 * x + 1) else 0 := by
    intro x m
    rw [PowerSeries.coeff_C_mul_X_pow]
  -- The sum over range (m+1) equals sum over range n because:
  -- 1. For x ≥ m+1: tri x ≥ x > m, so term is 0
  -- 2. For x ≥ n: tri x ≥ tri n > d ≥ m, so term is 0
  have h1 : ∀ x, x ≥ m + 1 → (if m = tri x then (-1 : ZMod 7) ^ x * (2 * x + 1) else 0) = 0 := by
    intro x hx
    simp only [ite_eq_right_iff]
    intro heq
    have : x ≤ tri x := self_le_tri x
    omega
  have h2 : ∀ x, x ≥ n → (if m = tri x then (-1 : ZMod 7) ^ x * (2 * x + 1) else 0) = 0 := by
    intro x hx
    simp only [ite_eq_right_iff]
    intro heq
    have htri : tri n ≤ tri x := tri_strictMono.monotone hx
    by_cases heq2 : x = n
    · rw [heq2] at heq; omega
    · have : n < x := lt_of_le_of_ne hx (Ne.symm heq2)
      have htri' : tri n < tri x := tri_strictMono this
      omega
  -- Both sums equal sum over range (max n (m+1))
  set N := max n (m + 1)
  have lhs_eq := Finset.sum_subset (Finset.range_mono (le_max_left n (m + 1)))
    (fun x _ hx => h2 x (Nat.not_lt.mp (Finset.mem_range.not.mp hx)))
  have rhs_eq := Finset.sum_subset (Finset.range_mono (le_max_right n (m + 1)))
    (fun x _ hx => h1 x (Nat.not_lt.mp (Finset.mem_range.not.mp hx)))
  have hconvert : ∀ x ∈ range n, ((-1 : S7) ^ x * (C (2 : ZMod 7) * (x : S7) + 1) * X ^ tri x) =
                       C ((-1 : ZMod 7) ^ x * (2 * (x : ZMod 7) + 1)) * X ^ tri x := by
    intro x _
    have : ((-1 : S7) ^ x * (C (2 : ZMod 7) * (x : S7) + 1)) = C ((-1 : ZMod 7) ^ x * (2 * (x : ZMod 7) + 1)) := by
      simp [mul_add, mul_comm]
    rw [this]
  rw [Finset.sum_congr rfl (fun x hx => by rw [hconvert x hx]),
      Finset.sum_congr rfl (fun x hx => coeff_term x m), lhs_eq, ← rhs_eq]
  simp_rw [eq_comm]

/-- A congruence between two terms of the key sums, from a congruence of the factors. -/
