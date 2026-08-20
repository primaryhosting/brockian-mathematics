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

lemma conj_posDef {k : ℕ} (A U : Matrix (Fin k) (Fin k) ℤ) (hpos : PosDefZ A) (hU : U.det = 1) :
    PosDefZ (Uᵀ * A * U) := by
  intro v hv
  rw [QF_conj]
  apply hpos
  intro heq
  obtain ⟨T, hTU, hUT⟩ := exists_inv_of_det_one U hU
  have key : v = T *ᵥ (U *ᵥ v) := by
    have h1 : (T * U) *ᵥ v = T *ᵥ (U *ᵥ v) := (Matrix.mulVec_mulVec v T U).symm
    rw [hUT] at h1
    simp [h1.symm]
  rw [heq] at key
  simp at key
  exact hv key

