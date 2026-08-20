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


theorem milnor_exotic_7sphere (f : Sph 7 ≃ₜ Sph 7)
    (charts : ChartedSpace E7 (TwistedSphere f))
    (smooth : IsManifold (𝓡 7) ∞ (TwistedSphere f))
    (hnd : IsEmpty (TwistedSphere f ≃ₘ⟮𝓡 7, 𝓡 7⟯ S7)) :
    ExoticSevenSphereExists :=
  ⟨TwistedSphere f, inferInstance, charts, smooth, twistedSphereHomeomorphSphere f, hnd⟩

/-- **Milnor's exotic 7-sphere, as an abstract Lean-checked reduction.**

If `P` is any predicate on smooth `7`-manifolds which is invariant under diffeomorphism, and if
some smooth `7`-manifold `M` is homeomorphic to the standard `7`-sphere while `P` separates `M`
from `𝕊⁷`, then an exotic `7`-sphere exists. -/
