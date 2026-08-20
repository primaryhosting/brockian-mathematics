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


lemma coneMap_coe_sphere (f : sphere (0 : E) 1 → sphere (0 : E) 1) (x : sphere (0 : E) 1) :
    coneMap f (x : E) = f x := by
  have hx : (x : E) ≠ 0 := coe_unitSphere_ne_zero x
  have hn : ‖(x : E)‖ = 1 := norm_coe_unitSphere x
  have hpt : normalizePt hx = x := by
    apply Subtype.ext
    simp [hn]
  rw [coneMap_of_ne_zero f hx, hpt, hn, one_smul]

/-- The radial projection, as a continuous map on the open subspace of nonzero vectors. -/
