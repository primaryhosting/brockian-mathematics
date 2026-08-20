import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
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

namespace Math2

/-- The affine cuspidal cubic `{(x, y) | y ^ 2 = x ^ 3}` over a field `k`. -/

theorem hironaka_resolution_closedEmbedding_real :
    Topology.IsClosedEmbedding (cuspRes ℝ) ∧ Set.range (cuspRes ℝ) = cuspCurve ℝ := by
  have hcont : Continuous (cuspRes ℝ) := by
    unfold cuspRes; fun_prop
  refine ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont
    cuspRes_injective hironaka_resolution_proper_real.isClosedMap, ?_⟩
  apply Set.Subset.antisymm
  · rintro p ⟨t, rfl⟩
    exact cuspRes_mem t
  · intro p hp
    exact ⟨cuspRes.inv ℝ p, cuspRes_cuspRes_inv hp⟩

end Math2

