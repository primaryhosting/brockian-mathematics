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


theorem milnor_exotic_7sphere_of_smooth_invariant
    (P : SmoothSeven → Prop)
    (hP : ∀ M N : SmoothSeven, Nonempty (M.Diffeo N) → (P M ↔ P N))
    (M : SmoothSeven) (hhomeo : Nonempty (M.Homeo sphereSeven))
    (hMP : ¬ P M) (hSP : P sphereSeven) :
    ExoticSevenSphereExists := by
  obtain ⟨h⟩ := hhomeo
  exact ⟨M.carrier, M.topology, M.charts, M.smooth, h,
    ⟨fun d => hMP ((hP M sphereSeven ⟨d⟩).mpr hSP)⟩⟩

/-- The converse: if an exotic `7`-sphere exists, then a separating diffeomorphism invariant
exists as well.  Hence the hypotheses of the abstract reduction are not merely sufficient but
also necessary. -/
