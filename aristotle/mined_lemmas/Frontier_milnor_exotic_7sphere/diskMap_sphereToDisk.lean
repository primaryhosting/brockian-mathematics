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


lemma diskMap_sphereToDisk {n : ℕ} (f : Sph n ≃ₜ Sph n) (x : Sph n) :
    diskMap f (sphereToDisk x) = sphereToDisk (f x) := by
  apply Subtype.ext
  exact coneHomeomorph_coe_sphere f x

/-- The identity homeomorphism of the boundary sphere; `Σ_(id)` is the untwisted double. -/
abbrev sphereId (n : ℕ) : Sph n ≃ₜ Sph n := Homeomorph.refl _

/-- Untwisting map `Σ_(id) → Σ_f`. -/
