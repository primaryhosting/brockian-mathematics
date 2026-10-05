import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/

theorem gleason_of_frameRepresentation (hFrame : FrameRepresentation n)
    (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) (hmu : IsQuantumMeasure mu) :
    ∃ rho : Matrix (Fin n) (Fin n) ℂ, IsDensityOperator rho ∧
      ∀ P : Matrix (Fin n) (Fin n) ℂ, IsProj P → ((mu P : ℝ) : ℂ) = (rho * P).trace := by
  obtain ⟨rho, hrho, hframe⟩ := hFrame mu hmu
  refine ⟨rho, ⟨posSemidef_of_frame hmu hrho hframe, ?_⟩, fun P hP =>
    trace_formula_of_frame hmu hframe hP⟩
  have h := trace_formula_of_frame hmu hframe (P := 1) isProj_one
  rw [mul_one, hmu.normalized] at h
  exact h.symm

/-- **Gleason's theorem** (reduction form).  On a complex Hilbert space of dimension `n ≥ 3`,
granted Gleason's analytic core `FrameRepresentation n`, every quantum measure is given by
a density operator: `mu P = tr (rho P)`.

The hypothesis `3 ≤ n` is the dimension hypothesis of Gleason's theorem; it is exactly what
is needed for `FrameRepresentation n` to hold, and is not used again in this reduction. -/
