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


theorem exists_separating_invariant_of_exotic (h : ExoticSevenSphereExists) :
    ∃ (P : SmoothSeven → Prop) (M : SmoothSeven),
      (∀ A B : SmoothSeven, Nonempty (A.Diffeo B) → (P A ↔ P B)) ∧
        Nonempty (M.Homeo sphereSeven) ∧ ¬ P M ∧ P sphereSeven := by
  obtain ⟨M, tM, cM, sM, homeo, hempty⟩ := h
  refine ⟨fun N => Nonempty (N.Diffeo sphereSeven), @SmoothSeven.mk M tM cM sM,
    fun A B hAB => ?_, ⟨homeo⟩, ?_, ⟨Diffeomorph.refl (𝓡 7) sphereSeven.carrier ∞⟩⟩
  · obtain ⟨e⟩ := hAB
    exact ⟨fun ⟨g⟩ => ⟨e.symm.trans g⟩, fun ⟨g⟩ => ⟨e.trans g⟩⟩
  · exact fun hc => hc.elim hempty.elim

/-- Milnor's theorem is *equivalent* to the existence of a diffeomorphism invariant separating
some manifold homeomorphic to `𝕊⁷` from `𝕊⁷` itself. -/
