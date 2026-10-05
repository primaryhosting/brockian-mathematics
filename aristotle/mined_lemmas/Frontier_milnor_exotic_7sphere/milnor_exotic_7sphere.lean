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

theorem milnor_exotic_7sphere
    (M : ℤ → Smooth7Manifold)
    (hHomeo : ∀ h : ℤ, Smooth7Manifold.Homeomorphic (M h) standardSphere7)
    (lam : Smooth7Manifold → ZMod 7)
    (hlam_inv : ∀ A B : Smooth7Manifold, Smooth7Manifold.Diffeomorphic A B → lam A = lam B)
    (hlam_M : ∀ h : ℤ, lam (M h) = milnorLambda h)
    (hlam_std : lam standardSphere7 = 0) :
    ∃ N : Smooth7Manifold,
      Smooth7Manifold.Homeomorphic N standardSphere7 ∧
        ¬ Smooth7Manifold.Diffeomorphic N standardSphere7 := by
  refine ⟨M 2, hHomeo 2, ?_⟩
  intro hdiff
  have h1 : lam (M 2) = lam standardSphere7 := hlam_inv _ _ hdiff
  rw [hlam_M 2, hlam_std] at h1
  exact milnorLambda_two_ne_zero h1

end Frontier

