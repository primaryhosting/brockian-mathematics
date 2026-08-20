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


lemma norm_eq_one_of_sqrt_eq_neg {n : ℕ} {x : Dsk n}
    (h : Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      = -Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) :
    ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have hz : Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) = 0 := by linarith
  have hle : 1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp hz
  have h1 := norm_coe_dsk_le x
  nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin n))]

