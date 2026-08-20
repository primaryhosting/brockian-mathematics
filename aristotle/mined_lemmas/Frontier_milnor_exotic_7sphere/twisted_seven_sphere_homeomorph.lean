import Mathlib
import RequestProject.AlexanderTrick

/-!
# Twisted spheres

A *twisted sphere* is obtained by gluing two copies of the closed `n`-disk along their boundary
`𝕊ⁿ⁻¹` by a homeomorphism `f`.  All the known exotic spheres in dimension `7` arise this way
(Milnor's `S³`-bundles over `S⁴` carry Morse functions with exactly two critical points, which exhibits
them as twisted spheres).

The main result of this file is that **every twisted sphere is homeomorphic to the standard
sphere**: this is the topological half of Milnor's theorem, and it is proved here in full, for
every dimension `n`, using the Alexander trick from `RequestProject.AlexanderTrick`.
-/

namespace Frontier

open Metric

/-- The unit sphere `𝕊ⁿ⁻¹ ⊆ ℝⁿ`. -/
abbrev Sph (n : ℕ) : Type := sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The closed unit disk `Dⁿ ⊆ ℝⁿ`. -/
abbrev Dsk (n : ℕ) : Type := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1


theorem twisted_seven_sphere_homeomorph (f : Sph 7 ≃ₜ Sph 7) :
    Nonempty (TwistedSphere f ≃ₜ S7) :=
  ⟨twistedSphereHomeomorphSphere f⟩

/-! ## Bundled smooth 7-manifolds

To speak about invariants of smooth `7`-manifolds we bundle the data. -/

/-- A bundled smooth `7`-manifold: a type together with a topology, an atlas modelled on
`ℝ⁷`, and the smoothness condition. -/
structure SmoothSeven where
  /-- The underlying type of the manifold. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charts : ChartedSpace E7 carrier]
  [smooth : IsManifold (𝓡 7) ∞ carrier]

attribute [instance] SmoothSeven.topology SmoothSeven.charts SmoothSeven.smooth

/-- Diffeomorphisms between bundled smooth `7`-manifolds. -/
abbrev SmoothSeven.Diffeo (M N : SmoothSeven) : Type :=
  M.carrier ≃ₘ⟮𝓡 7, 𝓡 7⟯ N.carrier

/-- Homeomorphisms between bundled smooth `7`-manifolds. -/
abbrev SmoothSeven.Homeo (M N : SmoothSeven) : Type :=
  M.carrier ≃ₜ N.carrier

/-- The standard `7`-sphere as a bundled smooth `7`-manifold. -/
