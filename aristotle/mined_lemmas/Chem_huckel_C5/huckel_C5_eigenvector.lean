/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

theorem huckel_C5_eigenvector (k : Fin 5) :
    ∃ v : Fin 5 → ℝ, v ≠ 0 ∧
      C5adj.mulVec v = (2 * Real.cos (2 * π * (k : ℕ) / 5)) • v := by
  set m : ℝ := 2 * Real.cos (2 * π * (k : ℕ) / 5) with hm
  have hmem : m ∈ spectrum ℝ C5adj := by
    rw [huckel_C5]
    exact ⟨k, rfl⟩
  have hdet : (algebraMap ℝ (Matrix (Fin 5) (Fin 5) ℝ) m - C5adj).det = 0 := by
    rw [mem_spectrum_C5adj_iff] at hmem
    rw [det_algebraMap_sub_C5adj]
    exact hmem
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, ?_⟩
  have halg : (algebraMap ℝ (Matrix (Fin 5) (Fin 5) ℝ) m).mulVec v = m • v := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, halg, sub_eq_zero] at hv
  exact hv.symm

end Chem

