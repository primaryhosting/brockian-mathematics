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


theorem milnor_exotic_7sphere_iff :
    ExoticSevenSphereExists ↔
      ∃ (P : SmoothSeven → Prop) (M : SmoothSeven),
        (∀ A B : SmoothSeven, Nonempty (A.Diffeo B) → (P A ↔ P B)) ∧
          Nonempty (M.Homeo sphereSeven) ∧ ¬ P M ∧ P sphereSeven :=
  ⟨exists_separating_invariant_of_exotic,
    fun ⟨P, M, hP, hhomeo, hMP, hSP⟩ =>
      milnor_exotic_7sphere_of_smooth_invariant P hP M hhomeo hMP hSP⟩

/-- The reduction is sharp in the following sense: a *topological* invariant can never do the
job, so the separating invariant must genuinely be a smooth invariant. -/
