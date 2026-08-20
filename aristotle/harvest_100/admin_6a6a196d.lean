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

import Mathlib
/-!
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module doc comments, so the required header comment is placed immediately after
-- the single `import Mathlib` line.

namespace Math

/-- **Heine–Borel theorem** for `ℝ^n`: a subset of Euclidean `n`-space is compact
if and only if it is closed and bounded, where boundedness is spelled out
concretely as the existence of a radius `r` with `‖x‖ ≤ r` for all `x` in the set. -/
theorem heine_borel {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ ∃ r : ℝ, ∀ x ∈ s, ‖x‖ ≤ r := by
  rw [Metric.isCompact_iff_isClosed_bounded, isBounded_iff_forall_norm_le]

end Math

