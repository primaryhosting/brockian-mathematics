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

lemma block_posDef (p q r : ℤ) (h : PosDefZ (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ)) :
    PosDefZ (!![p, q; q, r] : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro v hv_ne
  -- Extend v to a 3-vector by prepending 0
  let w : Fin 3 → ℤ := ![0, v 0, v 1]
  have hw_ne : w ≠ 0 := by
    intro hw_eq
    apply hv_ne
    funext i
    fin_cases i <;> have := congrFun hw_eq 1 <;> have := congrFun hw_eq 2 <;> simp [w] at * <;> linarith
  have hw_pos := h w hw_ne
  -- Now show QF of 3x3 on w equals QF of 2x2 on v
  simp [QF, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hw_pos ⊢
  simp [w] at hw_pos ⊢
  ring_nf at hw_pos ⊢
  exact hw_pos

