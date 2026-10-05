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

theorem not_exists_density_for_qubitMeasure :
    ¬ ∃ rho : Matrix (Fin 2) (Fin 2) ℂ, IsDensityOperator rho ∧
      ∀ P : Matrix (Fin 2) (Fin 2) ℂ, IsProj P →
        ((qubitMeasure P : ℝ) : ℂ) = (rho * P).trace := by
  rintro ⟨rho, ⟨-, htr⟩, hrep⟩
  have key : ∀ v : Fin 2 → ℂ, IsUnitVec v →
      ((qubitMeasure (rankOneProj v) : ℝ) : ℂ) = star v ⬝ᵥ (rho *ᵥ v) := fun v hv => by
    rw [hrep _ (isProj_rankOneProj hv), trace_mul_rankOneProj]
  have h0 := key e0 isUnitVec_e0
  have hp := key wPlus isUnitVec_wPlus
  have hm := key wMinus isUnitVec_wMinus
  rw [qubitMeasure_rankOne_e0] at h0
  rw [qubitMeasure_rankOne_wPlus] at hp
  rw [qubitMeasure_rankOne_wMinus] at hm
  simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Pi.star_apply, e0, wPlus, wMinus,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀, map_ofNat,
    RCLike.star_def, map_neg, map_one, map_zero, Complex.ofReal_one] at h0 hp hm
  have hrho00 : rho 0 0 = 1 := by linear_combination -h0
  have hrho11 : rho 1 1 = 0 := by
    have h : rho.trace = rho 0 0 + rho 1 1 := by rw [Matrix.trace, Fin.sum_univ_two]; rfl
    rw [htr, hrho00] at h
    linear_combination -h
  rw [hrho00, hrho11] at hp hm
  have hcontra : (2 : ℂ) = 32 / 25 := by linear_combination hp + hm
  norm_num at hcontra

/-- Gleason's analytic core fails in dimension two. -/
