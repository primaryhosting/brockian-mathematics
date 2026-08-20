/-
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Heine–Borel theorem**: a subset of `ℝ^n` (with the Euclidean metric) is compact
if and only if it is closed and bounded. -/
theorem heine_borel (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s :=
  Metric.isCompact_iff_isClosed_bounded

/-- **Heine–Borel theorem**, with boundedness spelled out as a uniform bound on the norm:
a subset of `ℝ^n` is compact iff it is closed and contained in some ball around the origin. -/
theorem heine_borel_norm (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ ∃ C : ℝ, ∀ x ∈ s, ‖x‖ ≤ C := by
  rw [heine_borel, isBounded_iff_forall_norm_le]

end Math

