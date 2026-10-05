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

theorem nbhd_union_subset {r : ℝ} {X Z : Set Site} {p : Site}
    (hp : p ∈ Z) (hp' : p ∈ nbhd r X)
    (hZ : ∀ z ∈ Z, ∀ w ∈ Z, dist z w ≤ 1) :
    nbhd r X ∪ Z ⊆ nbhd (r + 1) X := by
  rintro z (⟨x, hx, hzx⟩ | hz)
  · exact ⟨x, hx, by linarith⟩
  · obtain ⟨x, hx, hpx⟩ := hp'
    refine ⟨x, hx, ?_⟩
    have h1 : dist z p ≤ 1 := hZ z hz p hp
    have := dist_triangle z p x
    linarith

/-- Iterated neighbourhoods: the `1`-neighbourhood of the `r`-neighbourhood is contained in
the `(r+1)`-neighbourhood. -/
