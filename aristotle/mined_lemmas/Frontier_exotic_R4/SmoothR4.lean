/-
/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-! ## Setting up the statement

We work with the model space `EuclideanSpace ℝ (Fin 4)` and the trivial model with corners
on it, so that "smooth manifold modelled on `E4`" means a genuine boundaryless smooth
`4`-manifold in Mathlib's sense. -/

/-- The model space `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- The (boundaryless) model with corners used throughout: `ℝ⁴` modelled on itself. -/
noncomputable abbrev I4 : ModelWithCorners ℝ E4 E4 := modelWithCornersSelf ℝ E4

/-- A *smooth manifold homeomorphic to `ℝ⁴`*: a topological space `carrier`, equipped with a
`C^∞` manifold structure modelled on `ℝ⁴`, together with a homeomorphism onto `ℝ⁴`.

Equivalently (and this is how it is used below) this is a smooth structure on the topological
space `ℝ⁴`, presented invariantly. -/
structure SmoothR4 : Type 1 where
  /-- The underlying set. -/
  carrier : Type
  /-- Its topology. -/
  topology : TopologicalSpace carrier
  /-- An atlas of charts with values in `ℝ⁴`. -/
  charts : @ChartedSpace E4 _ carrier topology
  /-- The atlas is `C^∞`-compatible, i.e. this is a smooth manifold. -/
  isManifold : @IsManifold ℝ _ E4 _ _ E4 _ I4 ⊤ carrier topology charts
  /-- The underlying topological space is homeomorphic to `ℝ⁴`. -/
  homeomorphicToR4 : Nonempty (@Homeomorph carrier E4 topology _)

attribute [instance] SmoothR4.topology SmoothR4.charts SmoothR4.isManifold

/-- Two smooth structures on `ℝ⁴` are *diffeomorphic* when there is a `C^∞` diffeomorphism
between them. -/

noncomputable def SmoothR4.ofHomeomorph (e : X ≃ₜ E4) : SmoothR4 where
  carrier := X
  topology := tX
  charts := chartedSpaceOfHomeomorph e
  isManifold := isManifold_chartedSpaceOfHomeomorph e
  homeomorphicToR4 := ⟨e⟩

/-- A space homeomorphic to `ℝ⁴`, equipped with the transported smooth structure, is not
exotic. -/
