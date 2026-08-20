/-
# Extreme Value
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.extreme_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Extreme Value
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.extreme_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option autoImplicit false

namespace Analysis

variable {X : Type*} [TopologicalSpace X]

/-- Key intermediate lemma: the continuous image of a nonempty compact set is a nonempty
compact set of reals, hence it is bounded above and contains its supremum. -/

theorem extreme_value {s : Set X} {f : X → ℝ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x := by
  obtain ⟨M, hM, hMmax⟩ := exists_mem_image_forall_le hs hne hf
  obtain ⟨x, hx, rfl⟩ := hM
  exact ⟨x, hx, fun y hy => hMmax (f y) ⟨y, hy, rfl⟩⟩

end Analysis

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

