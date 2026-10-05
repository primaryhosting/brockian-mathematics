/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open scoped Real
open Finset

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A primitive 17-th root of unity. -/

theorem huckel_C17_spectrum :
    spectrum ℂ (Matrix.toLin' adjC17)
      = {mu : ℂ | ∃ k : ℕ, k < 17 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 17) : ℝ) : ℂ)} := by
  ext mu
  rw [Set.mem_setOf_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum, ← huckel_C17 mu]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.mp hv.1
  · rintro ⟨v, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv0⟩
    simpa [Matrix.toLin'_apply] using hv

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

