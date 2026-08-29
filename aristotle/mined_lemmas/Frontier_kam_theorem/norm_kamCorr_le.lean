/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Real Finset RealInnerProductSpace

namespace Frontier

/-- One factor of phase space, `ℝⁿ`.  It is used both for the action variables `p`
and for the angle variables `q`; the angles are understood modulo the lattice `2π ℤⁿ`. -/
abbrev Phase (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The Fourier mode `k ∈ ℤⁿ`, viewed as a vector of `ℝⁿ`. -/

lemma norm_kamCorr_le (θ : Phase n) :
    ‖kamCorr ω K a b θ‖ ≤ ∑ k ∈ K, ((|a k| + |b k|) / |⟪mode k, ω⟫|) * ‖mode k‖ := by
  classical
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro k _
  rw [norm_smul, Real.norm_eq_abs, abs_div]
  have h2 : |a k * cos ⟪mode k, θ⟫| ≤ |a k| := by
    rw [abs_mul]
    nlinarith [abs_cos_le_one ⟪mode k, θ⟫, abs_nonneg (a k), abs_nonneg (cos ⟪mode k, θ⟫)]
  have h3 : |b k * sin ⟪mode k, θ⟫| ≤ |b k| := by
    rw [abs_mul]
    nlinarith [abs_sin_le_one ⟪mode k, θ⟫, abs_nonneg (b k), abs_nonneg (sin ⟪mode k, θ⟫)]
  have h1 : |a k * cos ⟪mode k, θ⟫ + b k * sin ⟪mode k, θ⟫| ≤ |a k| + |b k| :=
    (abs_add_le _ _).trans (by linarith)
  gcongr

end Homological

section Hamilton

variable (ω : Phase n) (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ) (ε : ℝ)

