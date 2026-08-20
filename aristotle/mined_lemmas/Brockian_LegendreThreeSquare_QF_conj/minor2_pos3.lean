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

lemma minor2_pos3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (hpos : PosDefZ A) :
    0 < A 0 0 * A 1 1 - A 0 1 ^ 2 := by
  -- First, use that A 0 0 > 0 (from positive definiteness with v = ![1, 0, 0])
  have h00 : 0 < A 0 0 := by
    have := hpos ![1, 0, 0] (by decide)
    simp [QF, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    exact this
  -- Use vector v = ![A 0 1, -A 0 0, 0]
  -- QF A v = A 0 0 * (A 0 1)^2 + 2 * A 0 1 * A 0 1 * (-A 0 0) + A 1 1 * (A 0 0)^2
  --        = A 0 0 * (A 0 0 * A 1 1 - A 0 1 ^ 2)
  let v : Fin 3 → ℤ := ![A 0 1, -A 0 0, 0]
  have hv_ne : v ≠ 0 := by
    intro hv_eq
    have := congrFun hv_eq 1
    simp [v] at this
    linarith
  have hv_pos := hpos v hv_ne
  simp [QF, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hv_pos
  simp [v] at hv_pos
  -- hv_pos should now be: 0 < A 0 1 * (A 0 0 * A 0 1 + A 0 1 * (-A 0 0)) + (-A 0 0) * (A 1 0 * A 0 1 + A 1 1 * (-A 0 0))
  -- Simplifies to: 0 < A 0 1 * (A 0 0 * A 0 1 - A 0 1 * A 0 0) + (-A 0 0) * (A 1 0 * A 0 1 - A 1 1 * A 0 0)
  -- = 0 < 0 + (-A 0 0) * (A 1 0 * A 0 1 - A 1 1 * A 0 0)
  -- = 0 < A 0 0 * (A 1 1 * A 0 0 - A 1 0 * A 0 1)
  -- Since A is symmetric, A 1 0 = A 0 1, so:
  -- = 0 < A 0 0 * (A 1 1 * A 0 0 - A 0 1 * A 0 1)
  -- = 0 < A 0 0 * (A 0 0 * A 1 1 - A 0 1 ^ 2)
  have hsym01 : A 1 0 = A 0 1 := by
    have : Aᵀ = A := hsym
    have := congr_fun (congr_fun this 1) 0
    simp at this
    exact this.symm
  -- At this point hv_pos : 0 < (-A 0 0) * (A 1 0 * A 0 1 + A 1 1 * (-A 0 0))
  -- which equals A 0 0 * (A 0 0 * A 1 1 - A 0 1 * A 1 0)
  rw [hsym01] at hv_pos
  nlinarith

/-! ## Forms of determinant one represent `1` -/

