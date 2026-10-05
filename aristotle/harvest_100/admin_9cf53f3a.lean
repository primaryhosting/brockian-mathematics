import Mathlib

/-!
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede any other syntax (including module
-- doc comments `/-! ... -/`), so the required header comment is placed immediately after
-- the single `import Mathlib` line.

namespace Math

/-- **Heine–Borel theorem** for `ℝ^n` (`EuclideanSpace ℝ (Fin n)`):
a subset is compact if and only if it is closed and bounded.

This follows from Mathlib's `Metric.isCompact_iff_isClosed_bounded`, which holds in any
proper metric space; `EuclideanSpace ℝ (Fin n)` is proper, being a finite-dimensional
normed space over `ℝ`. -/
theorem heine_borel (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s :=
  Metric.isCompact_iff_isClosed_bounded

/-- Heine–Borel with boundedness spelled out concretely: `s ⊆ ℝ^n` is compact iff it is
closed and contained in some ball around the origin. -/
theorem heine_borel_norm (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ ∃ C : ℝ, ∀ x ∈ s, ‖x‖ ≤ C := by
  rw [heine_borel, ← isBounded_iff_forall_norm_le]

end Math

#print axioms Math.heine_borel
#print axioms Math.heine_borel_norm

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

