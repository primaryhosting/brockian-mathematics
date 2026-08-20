import Mathlib

/-!
# The Bloch sphere

Pure states of a qubit are unit vectors `(a, b) ∈ ℂ²`.  Two such vectors describe the same
physical state when they differ by a *global phase*, i.e. by multiplication with a complex
number of modulus one.  This file shows that the set of pure qubit states modulo global phase
is in bijection with the points of the 2-sphere `S² ⊆ ℝ³`, via the *Bloch map*

`(a, b) ↦ (2 Re (a * conj b), 2 Im (a * conj b), |a|² - |b|²)`.
-/

namespace QC

open Complex ComplexConjugate

/-- A pure qubit state: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  unit : normSq a + normSq b = 1

/-- Two pure qubit states are physically equal when they differ by a global phase. -/

lemma euclidean_norm_three_eq_one_iff (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ = 1 ↔ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three]
  simp [sq_abs]

/-- The coordinate description `Sphere2` really is the unit sphere `S²` of `ℝ³`. -/
