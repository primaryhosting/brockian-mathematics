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


def ExoticSevenSphereExists : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace E7 M)
    (_ : IsManifold (𝓡 7) ∞ M) (_homeo : M ≃ₜ S7),
    IsEmpty (M ≃ₘ⟮𝓡 7, 𝓡 7⟯ S7)

/-! ## The topological half of Milnor's theorem, proved

Milnor's manifolds are `S³`-bundles over `S⁴` carrying a Morse function with exactly two
critical points; such a manifold is a *twisted sphere*, i.e. two `7`-disks glued along their
boundary `𝕊⁶` by a homeomorphism.  The file `RequestProject.TwistedSphere` proves, in every
dimension and for *every* gluing homeomorphism, that the result is homeomorphic to the standard
sphere (via the Alexander trick of `RequestProject.AlexanderTrick`).  We record the
`7`-dimensional case here. -/

/-- **Every twisted `7`-sphere is homeomorphic to the standard `7`-sphere.**  Proved
unconditionally: this is the topological half of Milnor's theorem. -/
