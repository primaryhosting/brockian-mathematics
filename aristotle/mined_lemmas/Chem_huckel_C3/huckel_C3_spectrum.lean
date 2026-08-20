/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
with `α = 0`, `β = 1`). -/

theorem huckel_C3_spectrum :
    spectrum ℝ adjC3 = {μ : ℝ | ∃ k : Fin 3, μ = 2 * Real.cos (2 * π * (k : ℕ) / 3)} := by
  ext μ
  have hspec : μ ∈ spectrum ℝ adjC3 ↔
      (μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - adjC3).det = 0 := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
    simp [Algebra.algebraMap_eq_smul_one, isUnit_iff_ne_zero]
  rw [hspec, Set.mem_setOf_eq, ← Matrix.exists_mulVec_eq_zero_iff]
  rw [← huckel_C3 μ]
  constructor
  · rintro ⟨v, hv, hA⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hA
    exact hA.symm
  · rintro ⟨v, hv, hA⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

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

