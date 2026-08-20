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

theorem minkowski_matrix {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hdet : M.det = 1) (r : ℝ)
    (hvol : (2 : ℝ≥0∞) ^ k < volume {x : Fin k → ℝ | ∑ i, (x i) ^ 2 < r}) :
    ∃ v : Fin k → ℤ, v ≠ 0 ∧ ∑ i, (M.mulVec (fun j => (v j : ℝ)) i) ^ 2 < r := by
  classical
  have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
  set b : Module.Basis (Fin k) ℝ (Fin k → ℝ) :=
    (Pi.basisFun ℝ (Fin k)).map (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin k)) M hu) with hbdef
  have hb : ∀ i j, b i j = M j i := by
    intro i j
    simp only [hbdef, Module.Basis.map_apply, Pi.basisFun_apply, Matrix.toLinearEquiv_apply]
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdetb : |(Matrix.of ⇑b).det| = 1 := by
    have h : (Matrix.of ⇑b) = Mᵀ := by ext i j; simpa using hb i j
    rw [h, Matrix.det_transpose, hdet, abs_one]
  obtain ⟨c, hc0, hcS⟩ := minkowski_basis b {x : Fin k → ℝ | ∑ i, (x i) ^ 2 < r}
    (convex_ellipsoid k r) (by intro x hx; simpa using hx) (by rw [hdetb]; simpa using hvol)
  refine ⟨c, hc0, ?_⟩
  have h2 : (∑ i, c i • b i) = M.mulVec (fun j => (c j : ℝ)) := by
    funext j
    simp only [Finset.sum_apply, zsmul_eq_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun x _ => by simp [hb x j]; ring
  rwa [h2] at hcS

