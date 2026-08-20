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

lemma jacobi_p_mod_n (n p : ℕ) (hpn : (p + 1) % n = 0) :
    jacobiSym (p : ℤ) n = jacobiSym (-1) n := by
  have h : (p : ℤ) ≡ -1 [ZMOD n] := by
    have hdvd : (n : ℤ) ∣ (p + 1) := by norm_cast; exact Nat.dvd_of_mod_eq_zero hpn
    exact Int.ModEq.symm (Int.modEq_of_dvd <| by simpa using hdvd)
  rw [jacobiSym.mod_left p n]
  rw [jacobiSym.mod_left (-1) n]
  simp [Int.ModEq] at h
  rw [h]

