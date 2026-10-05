/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Metric Set

namespace Brouwer2D

/-! ### The radial retraction of the plane onto the closed unit disk -/

/-- The radial retraction of `ℂ` onto the closed unit disk. -/

theorem brouwer_2d
    (f : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hf : Continuous f) : ∃ x, f x = x := by
  classical
  -- Identify the Euclidean plane with `ℂ` by a linear isometry.
  set e := Complex.orthonormalBasisOneI.repr
  have hmemD : ∀ z : ℂ, ‖z‖ ≤ 1 → e z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z hz
    simpa [mem_closedBall_zero_iff] using hz
  set P : ℂ → Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun z => ⟨e (Brouwer2D.diskProj z), hmemD _ (Brouwer2D.norm_diskProj_le z)⟩ with hP
  have hPc : Continuous P :=
    ((e.continuous.comp Brouwer2D.continuous_diskProj)).subtype_mk _
  set g : ℂ → ℂ := fun z => e.symm ((f (P z) : EuclideanSpace ℝ (Fin 2))) with hg
  have hgc : Continuous g :=
    e.symm.continuous.comp ((continuous_subtype_val.comp hf).comp hPc)
  have hgmaps : Set.MapsTo g (Metric.closedBall (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro z _
    have h2 := (f (P z)).2
    rw [mem_closedBall_zero_iff] at h2 ⊢
    simpa [hg] using h2
  obtain ⟨z, hz, hfz⟩ := Brouwer2D.brouwer_complex g hgc.continuousOn hgmaps
  rw [mem_closedBall_zero_iff] at hz
  have hpz : P z = ⟨e z, hmemD z hz⟩ := by
    simp [hP, Brouwer2D.diskProj_eq_self hz]
  refine ⟨P z, Subtype.ext ?_⟩
  have : (f (P z) : EuclideanSpace ℝ (Fin 2)) = e z := by
    have := congrArg e hfz
    simpa [hg] using this
  rw [this, hpz]

/-- Brouwer's fixed point theorem in dimension two, stated for a continuous map of the plane
mapping the closed unit disk into itself. -/
