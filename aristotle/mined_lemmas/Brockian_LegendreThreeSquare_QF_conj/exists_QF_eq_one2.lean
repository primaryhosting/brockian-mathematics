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

theorem exists_QF_eq_one2 (C : Matrix (Fin 2) (Fin 2) ℤ) (hsym : C.IsSymm) (hpos : PosDefZ C)
    (hdet : C.det = 1) : ∃ v : Fin 2 → ℤ, QF C v = 1 := by
  have h00 : 0 < C 0 0 := minor1_pos2 C hpos
  obtain ⟨c, hc_ne, hc_mem⟩ := minkowski2 (chol2Mat C) (chol2_det C h00)
  refine ⟨c, ?_⟩
  have hpos_val : 0 < QF C c := hpos c hc_ne
  have hreal : ((QF C c : ℤ) : ℝ) = ∑ i, ((chol2Mat C).mulVec (fun j => (c j : ℝ)) i) ^ 2 :=
    chol2_apply C hsym h00 hdet c
  have hlt : (QF C c : ℝ) < 13 / 10 := by rwa [hreal]
  have hle : QF C c ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have : (QF C c : ℝ) ≥ 2 := by exact_mod_cast hcon
    linarith
  omega

