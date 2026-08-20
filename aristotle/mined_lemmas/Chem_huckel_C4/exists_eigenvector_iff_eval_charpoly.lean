/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial

/-- The Hückel matrix of the carbon skeleton of cyclobutadiene, in units where the Coulomb
integral `α` is `0` and the resonance integral `β` is `1`: the adjacency matrix of the cycle
graph `C₄`. -/

lemma exists_eigenvector_iff_eval_charpoly (A : Matrix (Fin 4) (Fin 4) ℝ) (μ : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v) ↔ A.charpoly.eval μ = 0 := by
  have hs : ∀ v : Fin 4 → ℝ, (Matrix.scalar (Fin 4) μ).mulVec v = μ • v := by
    intro v
    ext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, h, hs, sub_self]⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at h
    rw [← h, hs]

/-- **Hückel theory for cyclobutadiene (C₄).**

The characteristic polynomial of the adjacency matrix of the cycle graph `C₄` factors as
`∏_{k=0}^{3} (X - 2cos(2πk/4))`, and consequently the eigenvalues of that matrix (the real
numbers admitting a nonzero eigenvector) are exactly the numbers `2cos(2πk/4)` for
`k = 0, 1, 2, 3`, i.e. `2, 0, -2, 0`. -/
