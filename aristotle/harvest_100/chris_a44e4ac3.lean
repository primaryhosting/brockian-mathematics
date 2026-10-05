/-
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- NOTE: in this Lean version a module docstring (`/-! ... -/`) may not precede the
-- `import` line, so the required header appears above as a plain block comment and
-- again below, verbatim, as the module docstring.
import Mathlib

/-!
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Heine–Borel theorem** for `ℝ^n` (with the Euclidean metric): a subset of
`EuclideanSpace ℝ (Fin n)` is compact if and only if it is closed and bounded.

This is an instance of the general Mathlib result
`Metric.isCompact_iff_isClosed_bounded`, valid in any proper metric space;
`EuclideanSpace ℝ (Fin n)` is proper, being a finite-dimensional real normed space. -/
theorem heine_borel (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s :=
  Metric.isCompact_iff_isClosed_bounded

/-- Heine–Borel with boundedness spelled out as "the norms of the points of `s` are
uniformly bounded", stated for the product space `Fin n → ℝ`. -/
theorem heine_borel_norm_le (n : ℕ) (s : Set (Fin n → ℝ)) :
    IsCompact s ↔ IsClosed s ∧ ∃ r : ℝ, ∀ x ∈ s, ‖x‖ ≤ r := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h.subset_closedBall 0
    exact ⟨r, fun x hx => by simpa using Metric.mem_closedBall.mp (hr hx)⟩
  · rintro ⟨r, hr⟩
    refine Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := r)) fun x hx => ?_
    simpa using hr x hx

end Math

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

