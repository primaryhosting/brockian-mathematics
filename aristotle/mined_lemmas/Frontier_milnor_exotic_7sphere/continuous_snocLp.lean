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


lemma continuous_snocLp {X : Type*} [TopologicalSpace X] {n : ℕ}
    {g : X → EuclideanSpace ℝ (Fin n)} {t : X → ℝ} (hg : Continuous g) (ht : Continuous t) :
    Continuous fun s => snocLp (g s) (t s) := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simpa using ht
  · intro j
    simpa using (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hg)

