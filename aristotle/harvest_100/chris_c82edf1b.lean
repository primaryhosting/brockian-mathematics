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

/-- **Heine–Borel theorem.** A subset of `ℝ^n` (`n`-dimensional Euclidean space)
is compact if and only if it is closed and bounded. -/
theorem heine_borel (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s := by
  constructor
  · intro hs
    exact ⟨hs.isClosed, hs.isBounded⟩
  · rintro ⟨hclosed, hbdd⟩
    exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

/-- Metric-space phrasing of boundedness: a subset of `ℝ^n` is compact iff it is
closed and contained in some ball, i.e. its points have uniformly bounded distance. -/
theorem heine_borel_dist (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ ∃ C, ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C := by
  rw [heine_borel]
  constructor
  · rintro ⟨hc, hb⟩
    exact ⟨hc, (Metric.isBounded_iff.mp hb).imp fun _ h x hx y hy => h hx hy⟩
  · rintro ⟨hc, C, hC⟩
    exact ⟨hc, Metric.isBounded_iff.mpr ⟨C, fun {_} hx {_} hy => hC _ hx _ hy⟩⟩

end Math

