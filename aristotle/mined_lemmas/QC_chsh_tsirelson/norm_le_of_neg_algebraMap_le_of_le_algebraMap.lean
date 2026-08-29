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
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open scoped RealInnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a unital C⋆-algebra, a self-adjoint element sandwiched between `-r` and `r`
(as multiples of the unit) has norm at most `r`. -/

theorem norm_le_of_neg_algebraMap_le_of_le_algebraMap
    {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r)
    (h₁ : algebraMap ℝ A (-r) ≤ a) (h₂ : a ≤ algebraMap ℝ A r) : ‖a‖ ≤ r := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim a 0] using hr
  · rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
    · exact (le_algebraMap_iff_spectrum_le (R := ℝ) ha).mp h₂ _ h
    · have := (algebraMap_le_iff_le_spectrum (R := ℝ) ha).mp h₁ _ h
      linarith

/-- Negating both of the `B` observables of a CHSH tuple again yields a CHSH tuple. -/
