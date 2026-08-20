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

/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Chem

/-- Adjacency matrix of the cycle graph `C₆` (the Hückel connectivity matrix of benzene):
vertex `i` is adjacent to `i ± 1 mod 6`. -/

lemma spectrum_C6adj :
    {μ : ℂ | Module.End.HasEigenvalue (Matrix.toLin' C6adj) μ} = {2, 1, -1, -2} := by
  ext μ
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have hvec : C6adj.mulVec v = μ • v := by
      have h' := hv.apply_eq_smul
      rwa [Matrix.toLin'_apply] at h'
    have hpoly := eigenvalue_poly hv.2 hvec
    rcases mul_eq_zero.1 hpoly with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact Or.inl (sub_eq_zero.1 h3)
        · exact Or.inr (Or.inl (sub_eq_zero.1 h3))
      · exact Or.inr (Or.inr (Or.inl (by linear_combination h2)))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h1)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact hasEigenvalue_of_eigenvector vTwo_ne_zero mulVec_vTwo
    · exact hasEigenvalue_of_eigenvector vOne_ne_zero mulVec_vOne
    · exact hasEigenvalue_of_eigenvector vNegOne_ne_zero mulVec_vNegOne
    · exact hasEigenvalue_of_eigenvector vNegTwo_ne_zero mulVec_vNegTwo

/-- `2 cos (2πk/6)` as a real number, cast into `ℂ`. -/
