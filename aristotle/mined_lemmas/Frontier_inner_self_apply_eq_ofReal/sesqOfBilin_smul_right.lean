/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace BigOperators

namespace Frontier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A *density operator* on a complex Hilbert space: a self-adjoint, positive semidefinite
operator of unit trace. -/
structure IsDensityOperator (ρ : H →ₗ[ℂ] H) : Prop where
  isSymmetric : ρ.IsSymmetric
  nonneg : ∀ v : H, 0 ≤ (⟪v, ρ v⟫_ℂ).re
  trace_one : ρ.trace ℂ H = 1

/-- A *quantum measure* (a state on the lattice of closed subspaces): a nonnegative, normalized,
orthogonally additive function on subspaces. -/
structure QuantumMeasure (μ : Submodule ℂ H → ℝ) : Prop where
  nonneg : ∀ S, 0 ≤ μ S
  top : μ ⊤ = 1
  additive : ∀ S T : Submodule ℂ H, S ≤ Tᗮ → μ (S ⊔ T) = μ S + μ T

/-- The quantum measure induced by a density operator `ρ`: `S ↦ tr (ρ ∘ P_S)`, where `P_S` is
the orthogonal projection onto `S`. -/

lemma sesqOfBilin_smul_right (c : ℂ) (x y : H) :
    sesqOfBilin B x (c • y) = c * sesqOfBilin B x y := by
  have hII : (Complex.I • (Complex.I • y) : H) = -y := by rw [smul_smul]; norm_num
  have hlin : ∀ w : H, B x (c • w) = c.re * B x w + c.im * B x (Complex.I • w) := by
    intro w
    have hy : c • w = (c.re : ℝ) • w + (c.im : ℝ) • (Complex.I • w) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
        smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im c).symm
    rw [hy, map_add, map_smul, map_smul]
    simp
  have h1 : B x (c • y) = c.re * B x y + c.im * B x (Complex.I • y) := hlin y
  have h2 : B x (Complex.I • (c • y)) = c.re * B x (Complex.I • y) - c.im * B x y := by
    rw [smul_comm, hlin (Complex.I • y), hII, map_neg]
    ring
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [sesqOfBilin, sesqOfBilin, h1, h2]
  push_cast
  linear_combination (-((B x y : ℂ) - Complex.I * (B x (Complex.I • y) : ℂ))) * hc
    + ((c.im : ℂ) * (B x (Complex.I • y) : ℂ)) * Complex.I_sq

omit [FiniteDimensional ℂ H] in
