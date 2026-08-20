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

noncomputable def sphere2Equiv : Sphere2 ≃ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 where
  toFun p :=
    ⟨(EuclideanSpace.equiv (Fin 3) ℝ).symm ![p.1.1, p.1.2.1, p.1.2.2], by
      rw [mem_sphere_zero_iff_norm, euclidean_norm_three_eq_one_iff]
      simpa using p.2⟩
  invFun w :=
    ⟨(w.1 0, w.1 1, w.1 2), by
      have := mem_sphere_zero_iff_norm.mp w.2
      exact (euclidean_norm_three_eq_one_iff _).mp this⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp

/-- Pure qubit states modulo global phase are in bijection with the unit sphere of `ℝ³`. -/
