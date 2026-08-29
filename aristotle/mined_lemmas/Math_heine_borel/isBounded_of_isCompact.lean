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

theorem isBounded_of_isCompact {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsCompact s) :
    IsBounded s :=
  hs.isBounded

/-- A bounded set in `ℝ^n` is contained in some closed ball centred at the origin. -/
