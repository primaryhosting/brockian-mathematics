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

theorem exists_unimodular_col3 (v : Fin 3 → ℤ) (w : Fin 3 → ℤ) (h : w ⬝ᵥ v = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det = 1 ∧ ∀ i, U i 0 = v i := by
  have hdot : w 0 * v 0 + w 1 * v 1 + w 2 * v 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three] using h
  by_cases hg : (Int.gcd (v 1) (v 2) : ℤ) = 0
  · -- Degenerate case: the last two coordinates vanish, so `v 0 = ±1`.
    obtain ⟨h1, h2⟩ := Int.gcd_eq_zero_iff.mp (by exact_mod_cast hg)
    have h0 : v 0 * v 0 = 1 := by
      rw [h1, h2] at hdot
      have hvw : v 0 * w 0 = 1 := by linarith
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hvw with h' | h' <;> rw [h'] <;> ring
    refine ⟨!![v 0, 0, 0; 0, 1, 0; 0, 0, v 0], ?_, ?_⟩
    · simp [Matrix.det_fin_three]
      linear_combination h0
    · intro i; fin_cases i <;> simp [h1, h2]
  · -- Main case: write `v 1 = g * a`, `v 2 = g * b` with `g = gcd (v 1) (v 2)`.
    obtain ⟨a, ha⟩ : ((Int.gcd (v 1) (v 2) : ℤ)) ∣ v 1 := Int.gcd_dvd_left _ _
    obtain ⟨b, hb⟩ : ((Int.gcd (v 1) (v 2) : ℤ)) ∣ v 2 := Int.gcd_dvd_right _ _
    set g : ℤ := (Int.gcd (v 1) (v 2) : ℤ) with hgdef
    set s : ℤ := Int.gcdA (v 1) (v 2) with hs
    set t : ℤ := Int.gcdB (v 1) (v 2) with ht
    have hst : v 1 * s + v 2 * t = g := (Int.gcd_eq_gcd_ab (v 1) (v 2)).symm
    have hab : a * s + b * t = 1 := by
      have hcan : g * (a * s + b * t) = g * 1 := by
        rw [ha, hb] at hst; linarith [hst]
      exact mul_left_cancel₀ hg hcan
    refine ⟨!![v 0, -(w 1 * a + w 2 * b), 0; v 1, a * w 0, -t; v 2, b * w 0, s], ?_, ?_⟩
    · rw [ha, hb] at hdot
      rw [ha, hb]
      simp [Matrix.det_fin_three]
      linear_combination (v 0 * w 0 + (w 1 * a + w 2 * b) * g) * hab + hdot
    · intro i; fin_cases i <;> simp

/-! ## Clearing the first row and column -/

