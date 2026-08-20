import Mathlib

/-!
# Legendre's three-square theorem

A natural number `n` is a sum of three squares if and only if it is not of the
form `4 ^ a * (8 * b + 7)`.

The proof is self-contained (only core `Mathlib` is used).  The hard direction
goes through the classical route:

* Minkowski's convex body theorem shows that every positive definite integral
  ternary quadratic form of determinant one represents `1`, hence (by descent)
  is of the shape `Nᵀ * N`.
* Dirichlet's theorem on primes in arithmetic progressions together with
  quadratic reciprocity produces, for every `n` with `n % 4 ≠ 0` and
  `n % 8 ≠ 7`, an integer `m > 0` with `n ∣ m + 1` and `-n` a square modulo `m`.
  Out of these data one builds an explicit positive definite integral ternary
  form of determinant one whose `(0,0)` entry is `n`.
-/

namespace Brockian.LegendreThreeSquare

open Matrix MeasureTheory
open scoped ENNReal

/-! ## Integral quadratic forms -/

/-- The value at `v` of the quadratic form attached to the integer matrix `A`. -/

theorem exists_aux_data (n m : ℕ) (hn : 3 ≤ n) (hm : 0 < m) (hdvd : n ∣ m + 1) (y : ℤ)
    (hy : (m : ℤ) ∣ y ^ 2 + n) :
    ∃ x c : ℤ, 0 < (n : ℤ) * c - 1 ∧ (n : ℤ) * (c * (m : ℤ) - x ^ 2) - (m : ℤ) = 1 := by
  have hnz : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  obtain ⟨D, hD⟩ : ∃ D : ℤ, (m : ℤ) + 1 = (n : ℤ) * D := by
    obtain ⟨d, hd⟩ := hdvd
    exact ⟨(d : ℤ), by exact_mod_cast congrArg (fun z : ℕ => (z : ℤ)) hd⟩
  have hDpos : 0 < D := by nlinarith
  obtain ⟨e, he⟩ := hy
  have hdvd2 : (m : ℤ) ∣ (y * D) ^ 2 + D := by
    refine ⟨D * D * e - D, ?_⟩
    have hexp : (y * D) ^ 2 + D = D * (D * (y ^ 2 + n) - (m : ℤ)) := by linear_combination D * hD
    rw [hexp, he]; ring
  obtain ⟨c, hc⟩ := hdvd2
  have hcpos : 0 < c := by nlinarith [sq_nonneg (y * D)]
  refine ⟨y * D, c, by nlinarith, ?_⟩
  have hcm : c * (m : ℤ) = (y * D) ^ 2 + D := by linarith [hc]
  rw [hcm]
  linarith [hD]

