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

theorem exists_QF_eq_one3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (hpos : PosDefZ A)
    (hdet : A.det = 1) : ∃ v : Fin 3 → ℤ, QF A v = 1 := by
  -- Get that the leading minors are positive
  have h00 : 0 < A 0 0 := minor1_pos3 A hpos
  have hd2 : 0 < A 0 0 * A 1 1 - A 0 1 ^ 2 := minor2_pos3 A hsym hpos
  -- chol3Mat A has det = 1
  have hdet_chol : (chol3Mat A).det = 1 := chol3_det A h00 hd2 hdet
  -- Use minkowski3 with chol3Mat A
  obtain ⟨c, hc_ne, hc_mem⟩ := minkowski3 (chol3Mat A) hdet_chol
  -- Show QF A c = 1
  use c
  have hpos_val : 0 < QF A c := hpos c hc_ne
  have hreal : ((QF A c : ℤ) : ℝ) = ∑ i, ((chol3Mat A).mulVec (fun j => (c j : ℝ)) i) ^ 2 := by
    apply chol3_apply A hsym h00 hd2 hdet
  -- Since QF A c is a positive integer < 19/10, it must be 1
  have hlt : (QF A c : ℝ) < 19 / 10 := by rwa [hreal]
  have hint : QF A c ≤ 1 := by
    by_contra h
    push_neg at h
    have : (QF A c : ℝ) ≥ 2 := by exact_mod_cast h
    linarith
  omega

/-! ## Completing a primitive vector to a basis -/

