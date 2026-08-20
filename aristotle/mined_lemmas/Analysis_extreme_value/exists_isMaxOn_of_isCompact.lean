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

/-- Key intermediate lemma: a continuous real-valued function on a nonempty compact set
attains a maximum in the sense of `IsMaxOn`. -/

theorem exists_isMaxOn_of_isCompact {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : s.Nonempty) (hsc : IsCompact s)
    {f : X → ℝ} (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMaxOn f s x :=
  hsc.exists_isMaxOn hs hf

/-- The extreme value theorem: a continuous real-valued function on a nonempty compact set
attains its maximum. -/
