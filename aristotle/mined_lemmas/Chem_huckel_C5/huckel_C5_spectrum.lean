/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`):
vertices are indexed by `Fin 5` with cyclic successor `i ↦ i + 1`, and `i, j` are adjacent
iff one is the cyclic successor of the other. -/

theorem huckel_C5_spectrum (μ : ℝ) :
    (∃ v ≠ 0, C5adj *ᵥ v = μ • v) ↔ ∃ k : ℕ, k < 5 ∧ μ = 2 * Real.cos (2 * π * k / 5) := by
  have hs : ∀ v : Fin 5 → ℝ, (Matrix.scalar (Fin 5) μ) *ᵥ v = μ • v := by
    intro v; ext i
    simp [Matrix.scalar, Matrix.mulVec, Matrix.diagonal, dotProduct, Finset.sum_ite_eq]
  have h1 : (∃ v ≠ 0, C5adj *ᵥ v = μ • v) ↔ (Matrix.scalar (Fin 5) μ - C5adj).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, by rw [Matrix.sub_mulVec, hs, h, sub_self]⟩
    · rintro ⟨v, hv, h⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hs, sub_eq_zero] at h
      exact h.symm
  rw [h1, ← Matrix.eval_charpoly, huckel_C5, Polynomial.eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mp hk, by linarith [sub_eq_zero.mp h]⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mpr hk, by rw [h]; ring⟩

end Chem

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

