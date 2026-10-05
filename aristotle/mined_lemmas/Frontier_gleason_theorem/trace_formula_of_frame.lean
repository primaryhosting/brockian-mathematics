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

theorem trace_formula_of_frame {mu : Matrix (Fin n) (Fin n) ℂ → ℝ} (hmu : IsQuantumMeasure mu)
    {rho : Matrix (Fin n) (Fin n) ℂ}
    (hframe : ∀ v : Fin n → ℂ, IsUnitVec v →
      ((mu (rankOneProj v) : ℝ) : ℂ) = (rho * rankOneProj v).trace)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P) :
    ((mu P : ℝ) : ℂ) = (rho * P).trace := by
  obtain ⟨s, b, hb, horth, hPeq⟩ := proj_eq_sum_rankOne hP
  rw [hPeq, hmu.sum_eq (fun j _ => isProj_rankOneProj (hb j)) (fun i _ j _ hij => horth i j hij),
    Finset.mul_sum, Matrix.trace_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ => hframe (b j) (hb j)

/-- Rescaling a vector rescales the associated quadratic form. -/
