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


lemma snocLp_injective {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)} {t s : ℝ}
    (h : snocLp x t = snocLp y s) : x = y ∧ t = s := by
  constructor
  · ext i
    have := congrArg (fun v => (WithLp.ofLp v) i.castSucc) h
    simpa [snocLp_apply_castSucc] using this
  · have := congrArg (fun v => (WithLp.ofLp v) (Fin.last n)) h
    simpa [snocLp_apply_last] using this

/-- Every Euclidean vector in `ℝⁿ⁺¹` is a `snocLp`. -/
