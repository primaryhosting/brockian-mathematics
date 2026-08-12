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

namespace Math

/-- **Heine–Borel theorem**: a subset of `ℝ^n` is compact if and only if it is
closed and bounded (boundedness expressed as a uniform bound on norms). -/
theorem heine_borel {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ ∃ R : ℝ, ∀ x ∈ s, ‖x‖ ≤ R := by
  rw [Metric.isCompact_iff_isClosed_bounded, isBounded_iff_forall_norm_le]

end Math

