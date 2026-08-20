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

lemma cos_values :
    {μ : ℂ | ∃ k : Fin 6, μ = 2 * Complex.cos (2 * (Real.pi : ℂ) * (k : ℕ) / 6)} =
      {2, 1, -1, -2} := by
  ext μ
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl cos_val_zero
    · exact Or.inr (Or.inl cos_val_one)
    · exact Or.inr (Or.inr (Or.inl cos_val_two))
    · exact Or.inr (Or.inr (Or.inr cos_val_three))
    · exact Or.inr (Or.inr (Or.inl cos_val_four))
    · exact Or.inr (Or.inl cos_val_five)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, cos_val_zero.symm⟩
    · exact ⟨1, cos_val_one.symm⟩
    · exact ⟨2, cos_val_two.symm⟩
    · exact ⟨3, cos_val_three.symm⟩

/-- **Hückel theory for benzene (C₆).** The eigenvalues of the adjacency matrix of the cycle
graph `C₆` are exactly the numbers `2 cos (2πk/6)` for `k = 0, …, 5`. -/
