import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
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

set_option grind.warning false

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

lemma antichainCoverNumbers_nonempty : (antichainCoverNumbers α).Nonempty := by
  refine ⟨Fintype.card α, fun i => {(Fintype.equivFin α).symm i}, ?_, ?_⟩
  · intro i a ha b hb hab
    simp only [Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · intro x
    exact ⟨Fintype.equivFin α x, by simp⟩

