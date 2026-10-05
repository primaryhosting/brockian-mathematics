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

lemma hasGradientAt_pert (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ) (θ : Phase n) :
    HasGradientAt (pert K a b) (gradPert K a b θ) θ := by
  classical
  rw [hasGradientAt_iff_hasFDerivAt]
  have : ∀ k ∈ K, HasFDerivAt (fun y : Phase n => a k * cos ⟪mode k, y⟫ + b k * sin ⟪mode k, y⟫)
      ((InnerProductSpace.toDual ℝ (Phase n))
        ((-(a k) * sin ⟪mode k, θ⟫ + b k * cos ⟪mode k, θ⟫) • mode k)) θ := by
    intro k _
    have hc := ((hasGradientAt_cos_inner (mode k) θ).hasFDerivAt).const_mul (a k)
    have hs := ((hasGradientAt_sin_inner (mode k) θ).hasFDerivAt).const_mul (b k)
    have := hc.add hs
    convert this using 1
    ext y
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      InnerProductSpace.toDual_apply_apply, real_inner_smul_left, smul_eq_mul]
    ring
  have hsum := HasFDerivAt.fun_sum this
  simp only [gradPert]
  convert hsum using 1
  simp

end Basic

section Homological

variable (ω : Phase n) (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)

/-- **The homological equation.**  Along the linear flow `t ↦ θ + t ω` on the torus, the
derivative of the correction `U` is exactly the gradient of the perturbation. -/
