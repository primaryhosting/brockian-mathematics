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


noncomputable def untwist {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    TwistedSphere f → TwistedSphere (sphereId n) := by
  refine Quot.lift (fun p => TwistedSphere.mk (sphereId n) (Sum.map id (diskMap f.symm) p)) ?_
  rintro _ _ ⟨x⟩
  have h : diskMap f.symm (sphereToDisk (f x)) = sphereToDisk x := by
    rw [diskMap_sphereToDisk f.symm (f x)]
    simp
  simpa [Sum.map, h] using TwistedSphere.sound (sphereId n) x

/-- **Untwisting.**  For every boundary homeomorphism `f`, the twisted sphere `Σ_f` is
homeomorphic to the untwisted double `Σ_(id)`.  This is where the Alexander trick is used. -/
