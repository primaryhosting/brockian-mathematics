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

theorem milnorLambda_eq_zero_iff (h : ℤ) :
    milnorLambda h = 0 ↔ ((h : ZMod 7) = 0 ∨ (h : ZMod 7) = 1) := by
  have : milnorLambda h = (2 * (h : ZMod 7) - 1) ^ 2 - 1 := by
    unfold milnorLambda; push_cast; ring
  rw [this]
  generalize ((h : ZMod 7)) = x
  revert x
  decide

/-- **Milnor's exotic 7-spheres (Lean-checked reduction).**

Given

* a family `M : ℤ → Smooth7Manifold` of smooth 7-manifolds (Milnor's `S³`-bundles over
  `S⁴` with clutching data `(h, 1 - h)`),
* the fact that each `M h` is homeomorphic to the standard 7-sphere,
* a `ZMod 7`-valued diffeomorphism invariant `lam` (Milnor's `λ`),
* the computation `lam (M h) = (2h - 1)^2 - 1` in `ZMod 7`,
* the vanishing `lam (standard 7-sphere) = 0`,

there exists a smooth 7-manifold which is homeomorphic to `S⁷` but **not** diffeomorphic
to `S⁷`; explicitly, `M 2` works.  The last step is the arithmetic base case
`milnorLambda_two_ne_zero`. -/
