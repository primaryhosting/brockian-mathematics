import Mathlib

/-!
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
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

namespace Math

/-- **Heine–Borel theorem** for `ℝ^n` (`EuclideanSpace ℝ (Fin n)`):
a subset is compact iff it is closed and bounded, where boundedness is expressed
concretely as the existence of a uniform bound on the norms of its elements.

The key ingredient from Mathlib is `Metric.isCompact_iff_isClosed_bounded`, which holds
in any proper metric space; `EuclideanSpace ℝ (Fin n)` is a finite-dimensional real
normed space and hence proper. -/
theorem heine_borel {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ ∃ C : ℝ, ∀ x ∈ s, ‖x‖ ≤ C := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hb
    obtain ⟨C, hC⟩ := hb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
    exact ⟨C, fun x hx => by simpa [Metric.mem_closedBall, dist_eq_norm] using hC hx⟩
  · rintro ⟨C, hC⟩
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := C)) ?_
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC x hx

end Math

