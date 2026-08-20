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


noncomputable def coneMap (f : sphere (0 : E) 1 → sphere (0 : E) 1) (x : E) : E :=
  if h : x = 0 then 0 else ‖x‖ • (f (normalizePt h) : E)

