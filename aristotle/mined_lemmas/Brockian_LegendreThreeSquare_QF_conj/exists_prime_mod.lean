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

lemma exists_prime_mod (M : ℕ) (hM : 0 < M) (r : ℕ) (hr : Nat.Coprime r M) (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p % M = r % M := by
  by_cases hM0 : M = 0
  · simp [hM0] at hM
  have h : Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ r [MOD M]} := by
    exact Nat.infinite_setOf_prime_and_modEq hM0 hr
  obtain ⟨p, hp, hpN⟩ := h.exists_gt N
  exact ⟨p, hp.1, hpN, by simpa using hp.2⟩

