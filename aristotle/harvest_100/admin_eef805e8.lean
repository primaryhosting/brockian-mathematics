import Mathlib

/-!
# Extreme Value
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.extreme_value
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Analysis

/-- **Extreme value theorem**: a real-valued function that is continuous on a nonempty
compact set `s` attains a maximum value on `s`, i.e. there is a point `x ∈ s` such that
`f y ≤ f x` for all `y ∈ s`. -/
theorem extreme_value {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsCompact s)
    (hne : s.Nonempty) {f : X → ℝ} (hf : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  let ⟨x, hxs, hx⟩ := IsCompact.exists_isMaxOn hs hne hf
  ⟨x, hxs, fun _ hy => hx hy⟩

end Analysis

