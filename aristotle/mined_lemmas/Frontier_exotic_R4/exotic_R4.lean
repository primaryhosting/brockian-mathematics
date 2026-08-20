/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Manifold ContDiff Topology

namespace Frontier

/-- The standard model space `ℝ⁴` (as a Euclidean space). -/
abbrev EuclideanR4 : Type := EuclideanSpace ℝ (Fin 4)

/-- A smooth (`C^∞`) `4`-manifold: a topological space with an atlas of charts modelled on
`ℝ⁴` whose transition maps are smooth. -/
structure SmoothManifold4 where
  /-- The underlying set of points. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charts : ChartedSpace EuclideanR4 carrier]
  [smooth : IsManifold (𝓡 4) ∞ carrier]

attribute [instance] SmoothManifold4.topology SmoothManifold4.charts SmoothManifold4.smooth

/-- `M` is an *exotic* `ℝ⁴`: it is homeomorphic to `ℝ⁴`, but there is no diffeomorphism
between `M` and `ℝ⁴` with its standard smooth structure. -/

theorem exotic_R4 (h : ExistsExoticOpenSubsetOfR4) :
    ∃ M : SmoothManifold4, IsExoticR4 M := by
  obtain ⟨U, hhomeo, hdiff⟩ := h
  exact ⟨⟨U⟩, hhomeo, hdiff⟩

end Frontier

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

