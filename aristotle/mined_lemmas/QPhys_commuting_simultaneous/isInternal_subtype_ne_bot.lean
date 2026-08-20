/-
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

open Module Module.End

/-- Restricting an internal direct sum decomposition to the indices whose summand is nonzero
still yields an internal direct sum decomposition. -/

theorem isInternal_subtype_ne_bot {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [DecidableEq ι] (V : ι → Submodule 𝕜 E) (hV : DirectSum.IsInternal V) :
    DirectSum.IsInternal (fun i : {i : ι // V i ≠ ⊥} ↦ V i.1) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨hV.submodule_iSupIndep.comp Subtype.val_injective, ?_⟩
  refine le_antisymm le_top ?_
  rw [← hV.submodule_iSup_eq_top]
  refine iSup_le fun i ↦ ?_
  by_cases hi : V i = ⊥
  · simp [hi]
  · exact le_iSup (fun j : {i : ι // V i ≠ ⊥} ↦ V j.1) ⟨i, hi⟩

/-- **Two commuting Hermitian (symmetric) operators are simultaneously diagonalizable.**

If `A` and `B` are symmetric (Hermitian) linear operators on a finite-dimensional inner
product space `E` over `𝕜 = ℝ` or `ℂ`, and they commute, then there is an orthonormal basis
of `E` each of whose vectors is simultaneously an eigenvector of `A` and of `B`.

The proof combines `LinearMap.IsSymmetric.directSum_isInternal_of_commute` (the decomposition
of `E` into an internal direct sum of joint eigenspaces of `A` and `B`) with
`DirectSum.IsInternal.subordinateOrthonormalBasis`. -/
