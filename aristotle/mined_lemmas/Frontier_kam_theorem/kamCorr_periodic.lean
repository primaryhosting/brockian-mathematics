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

lemma kamCorr_periodic (θ : Phase n) (m : Fin n → ℤ) :
    kamCorr ω K a b (θ + (2 * π) • mode m) = kamCorr ω K a b θ := by
  classical
  refine Finset.sum_congr rfl ?_
  intro k _
  have hint : ⟪mode k, mode m⟫ = ((∑ i, k i * m i : ℤ) : ℝ) := by
    simp [mode, PiLp.inner_apply, mul_comm]
  have : ⟪mode k, θ + (2 * π) • mode m⟫
      = ⟪mode k, θ⟫ + ((∑ i, k i * m i : ℤ) : ℝ) * (2 * π) := by
    rw [inner_add_right, real_inner_smul_right, hint]; ring
  rw [this, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- A uniform bound for the correction: the perturbed torus is `O(ε)`-close to the
unperturbed one. -/
