/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The `r`-neighbourhood of a set of sites `X` inside a metric space of sites. -/

theorem subset_nbhd {r : ℝ} (hr : 0 ≤ r) (X : Set Site) : X ⊆ nbhd r X := by
  intro x hx
  exact ⟨x, hx, by simpa using hr⟩

/-- If a gate region `Z` of diameter at most `1` meets the `k`-neighbourhood of `X`,
then the union of the two is contained in the `(k+1)`-neighbourhood of `X`. -/
