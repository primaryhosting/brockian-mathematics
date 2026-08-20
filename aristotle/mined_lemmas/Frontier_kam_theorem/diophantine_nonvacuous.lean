import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

variable {n : ℕ}

/-- Pairing of an integer covector `k` with a real vector `x`: `⟪k, x⟫ = ∑ i, k i * x i`. -/

theorem diophantine_nonvacuous (ω : Fin 1 → ℝ) (hω : ω 0 ≠ 0) :
    0 < |ω 0| ∧ ∀ k : Fin 1 → ℤ, k ≠ 0 → |ω 0| / (‖k‖ : ℝ) ^ (1 : ℝ) ≤ |dotIR k ω| := by
  refine ⟨abs_pos.mpr hω, fun k hk => ?_⟩
  have hk0 : k 0 ≠ 0 := by
    intro h
    exact hk (funext fun i => by fin_cases i; simpa using h)
  have hnorm : ‖k‖ = |((k 0 : ℤ) : ℝ)| := by
    have h1 : ‖(k 0 : ℤ)‖ ≤ ‖k‖ := norm_le_pi_norm k 0
    have h2 : ‖k‖ ≤ ‖(k 0 : ℤ)‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => ?_)
      fin_cases i; exact le_refl _
    have : ‖k‖ = ‖(k 0 : ℤ)‖ := le_antisymm h2 h1
    simpa [Int.norm_eq_abs] using this
  have hone : (1 : ℝ) ≤ |((k 0 : ℤ) : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |k 0| := Int.one_le_abs (by simpa using hk0)
    have h2 : (1 : ℝ) ≤ ((|k 0| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [Int.cast_abs] using h2
  have hpos : (0 : ℝ) < |((k 0 : ℤ) : ℝ)| := lt_of_lt_of_le one_pos hone
  have hdot : |dotIR k ω| = |((k 0 : ℤ) : ℝ)| * |ω 0| := by
    simp [dotIR, abs_mul]
  rw [hnorm, Real.rpow_one, hdot, div_le_iff₀ hpos]
  have h4 : |ω 0| ≤ |((k 0 : ℤ) : ℝ)| * |ω 0| :=
    le_mul_of_one_le_left (abs_nonneg _) hone
  have h5 : |((k 0 : ℤ) : ℝ)| * |ω 0| ≤ |((k 0 : ℤ) : ℝ)| * |ω 0| * |((k 0 : ℤ) : ℝ)| :=
    le_mul_of_one_le_right (by positivity) hone
  linarith

end Frontier

