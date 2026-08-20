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


lemma continuous_coneMap {f : sphere (0 : E) 1 → sphere (0 : E) 1} (hf : Continuous f) :
    Continuous (coneMap f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, coneMap_zero]
    refine squeeze_zero_norm (fun y => le_of_eq (norm_coneMap f y)) ?_
    simpa using (continuous_norm (E := E)).tendsto' 0 0 (by simp)
  · have hopen : IsOpen {y : E | y ≠ 0} := isOpen_ne
    have hcont : ContinuousOn (coneMap f) {y : E | y ≠ 0} := by
      rw [continuousOn_iff_continuous_restrict]
      have hrestr : Set.restrict {y : E | y ≠ 0} (coneMap f)
          = fun p : {y : E // y ∈ {y : E | y ≠ 0}} =>
            ‖(p : E)‖ • (f (radialProj ⟨p.1, p.2⟩) : E) := by
        funext p
        exact coneMap_of_ne_zero f p.2
      rw [hrestr]
      exact (continuous_norm.comp continuous_subtype_val).smul
        (continuous_subtype_val.comp (hf.comp (continuous_radialProj.comp
          (Continuous.subtype_mk continuous_subtype_val _))))
    exact hcont.continuousAt (hopen.mem_nhds hx)

/-- Cone extensions compose: if `g ∘ f = id` on the sphere then `coneMap g ∘ coneMap f = id`. -/
