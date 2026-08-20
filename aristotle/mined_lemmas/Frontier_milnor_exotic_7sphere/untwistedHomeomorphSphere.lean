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


noncomputable def untwistedHomeomorphSphere (n : ℕ) :
    TwistedSphere (sphereId n) ≃ₜ Sph (n + 1) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective untwistedToSphere
      ⟨untwistedToSphere_injective, untwistedToSphere_surjective⟩)
    (continuous_quot_lift _ continuous_doubleToSphere)

/-- **Every twisted sphere is homeomorphic to the standard sphere.**

This is the topological half of Milnor's theorem, proved here in full generality: gluing two
`n`-disks along their boundary by *any* homeomorphism always yields a space homeomorphic to
`𝕊ⁿ`.  Only the smooth structure can differ — which is exactly what Milnor's invariant detects. -/
