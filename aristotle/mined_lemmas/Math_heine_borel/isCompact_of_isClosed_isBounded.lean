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

open Metric Bornology

variable {n : ℕ}

/-- A compact subset of `ℝ^n` is closed (Euclidean space is Hausdorff). -/

theorem isCompact_of_isClosed_isBounded {s : Set (EuclideanSpace ℝ (Fin n))}
    (hclosed : IsClosed s) (hbdd : IsBounded s) : IsCompact s := by
  obtain ⟨r, hr⟩ := exists_subset_closedBall_of_isBounded hbdd
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
    hclosed hr

/-- **Heine–Borel theorem**: a subset of `ℝ^n` is compact if and only if it is closed and
bounded. -/
