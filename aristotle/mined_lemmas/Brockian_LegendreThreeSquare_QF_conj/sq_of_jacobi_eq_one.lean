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

lemma sq_of_jacobi_eq_one (p : ℕ) (hp : p.Prime) (a : ℤ) (hpa : ¬ (p : ℤ) ∣ a)
    (h : jacobiSym a p = 1) : ∃ y : ℤ, (p : ℤ) ∣ y ^ 2 - a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hleg : legendreSym p a = 1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact h
  have hne : ((a : ZMod p)) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hpa
  obtain ⟨z, hz⟩ := (legendreSym.eq_one_iff p hne).1 hleg
  refine ⟨(z.val : ℤ), ?_⟩
  have hcast : ((((z.val : ℤ)) ^ 2 - a : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, hz]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hcast

