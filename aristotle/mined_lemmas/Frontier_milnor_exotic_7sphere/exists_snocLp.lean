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


lemma exists_snocLp {n : ℕ} (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), v = snocLp x t := by
  refine ⟨WithLp.toLp 2 (Fin.init (WithLp.ofLp v)), (WithLp.ofLp v) (Fin.last n), ?_⟩
  apply WithLp.ofLp_injective
  simp [snocLp, Fin.snoc_init_self]

/-- The two hemisphere maps `Dⁿ → 𝕊ⁿ`, for `e = ±1`. -/
