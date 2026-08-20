/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean requires `import` to precede any module docstring `/-! ... -/`,
so this header is a plain block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix Polynomial

/-- A primitive 10-th root of unity. -/

theorem huckel_C10 :
    spectrum ℂ ((SimpleGraph.cycleGraph 10).adjMatrix ℂ)
        = {μ : ℂ | ∃ k : Fin 10, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 10)} ∧
      ((SimpleGraph.cycleGraph 10).adjMatrix ℂ).charpoly
        = ∏ k : Fin 10, (X - C (2 * (Real.cos (2 * Real.pi * (k : ℕ) / 10) : ℝ) : ℂ)) := by
  have hdet : IsUnit Pmat.det := isUnit_iff_ne_zero.mpr Pmat_det_ne_zero
  set u : (Matrix (Fin 10) (Fin 10) ℂ)ˣ := ((Matrix.isUnit_iff_isUnit_det Pmat).mpr hdet).unit
  have hu' : (u : Matrix (Fin 10) (Fin 10) ℂ) = Pmat := rfl
  have hconj : C10 = (u : Matrix (Fin 10) (Fin 10) ℂ) * Matrix.diagonal eig
      * ((u⁻¹ : (Matrix (Fin 10) (Fin 10) ℂ)ˣ) : Matrix (Fin 10) (Fin 10) ℂ) := by
    rw [Matrix.coe_units_inv, hu', ← C10_mul_Pmat, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  constructor
  · have : spectrum ℂ C10 = Set.range eig := by
      rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
    rw [show ((SimpleGraph.cycleGraph 10).adjMatrix ℂ) = C10 from rfl, this]
    ext μ
    simp only [Set.mem_range, Set.mem_setOf_eq, eig]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  · rw [show ((SimpleGraph.cycleGraph 10).adjMatrix ℂ) = C10 from rfl, hconj,
      Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
    rfl

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

