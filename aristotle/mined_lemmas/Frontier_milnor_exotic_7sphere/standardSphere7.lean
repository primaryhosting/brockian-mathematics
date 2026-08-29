import Mathlib

/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Manifold

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

/-! ## Smooth 7-manifolds

We package a smooth (`C^∞`) 7-dimensional manifold without boundary, modelled on
`EuclideanSpace ℝ (Fin 7)`, as a bundled structure so that we can quantify over such
objects. -/

/-- The model space for 7-dimensional smooth manifolds. -/
abbrev E7 : Type := EuclideanSpace ℝ (Fin 7)

/-- A bundled smooth (`C^∞`) 7-manifold without boundary. -/
structure Smooth7Manifold where
  /-- The underlying type of points. -/
  carrier : Type
  [top : TopologicalSpace carrier]
  [charted : ChartedSpace E7 carrier]
  [smooth : IsManifold (𝓘(ℝ, E7)) ⊤ carrier]

attribute [instance] Smooth7Manifold.top Smooth7Manifold.charted Smooth7Manifold.smooth

namespace Smooth7Manifold

/-- Two bundled smooth 7-manifolds are *homeomorphic* if their underlying topological
spaces are homeomorphic. -/

noncomputable def standardSphere7 : Smooth7Manifold where
  carrier := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

/-! ## Milnor's `λ`-invariant, the reduction, and the arithmetic base case

Milnor's construction produces, for each `h : ℤ`, a smooth 7-manifold `M h` (the total space
of the `S³`-bundle over `S⁴` with clutching data `(h, 1 - h)`).  Each `M h` is homeomorphic
to `S⁷`, because it carries a Morse function with exactly two critical points (Reeb's
theorem).  Milnor's `λ`-invariant, a diffeomorphism invariant of oriented smooth 7-manifolds
with values in `ZMod 7`, evaluates on `M h` to `(h - (1 - h))^2 - 1 = (2h - 1)^2 - 1`, and
vanishes on the standard sphere.

The arithmetic base case is that this quantity is nonzero mod `7` for a suitable `h`
(e.g. `h = 2`, giving `(h, l) = (2, -1)` and `λ = 8 ≡ 1`). -/

/-- Milnor's `λ`-invariant of the bundle `M_{h, 1-h}`, as an element of `ZMod 7`. -/
