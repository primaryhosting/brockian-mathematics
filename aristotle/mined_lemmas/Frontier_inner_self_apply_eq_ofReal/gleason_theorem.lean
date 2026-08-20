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

theorem gleason_theorem (hdim : 3 ≤ Module.finrank ℂ H) (μ : Submodule ℂ H → ℝ)
    (hμ : QuantumMeasure μ) (hcore : GleasonFrameProperty μ) :
    ∃ ρ : H →ₗ[ℂ] H, IsDensityOperator ρ ∧ ∀ S : Submodule ℂ H, μ S = traceMeasure ρ S := by
  classical
  obtain ⟨ρ, hsymm, hframe⟩ := hcore
  -- the measure of any subspace is the trace of `ρ` against its projection
  have key : ∀ S : Submodule ℂ H, μ S = traceMeasure ρ S := by
    intro S
    set b := stdOrthonormalBasis ℂ S with hb
    have hspan := iSup_span_singleton_orthonormalBasis b
    have horth := orthonormal_coe_orthonormalBasis b
    have hsum := hμ.sum_span_singleton horth (Finset.univ)
    rw [hspan] at hsum
    rw [hsum, traceMeasure_eq_sum b]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hframe _ (b.norm_eq_one i)
  refine ⟨ρ, ⟨hsymm, ?_, ?_⟩, key⟩
  · refine nonneg_of_nonneg_on_unit (fun v hv => ?_)
    rw [← hframe v hv]
    exact hμ.nonneg _
  · have htop := key ⊤
    rw [traceMeasure, Submodule.starProjection_top] at htop
    simp only [ContinuousLinearMap.coe_id, LinearMap.comp_id] at htop
    rw [hμ.top] at htop
    have hre : (ρ.trace ℂ H).re = 1 := htop.symm
    -- the trace is real because `ρ` is symmetric
    have hreal : ρ.trace ℂ H = ((ρ.trace ℂ H).re : ℂ) := by
      rw [LinearMap.trace_eq_sum_inner ρ (stdOrthonormalBasis ℂ H), Complex.re_sum,
        Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => inner_self_apply_eq_ofReal hsymm _
    rw [hreal, hre]
    norm_num

/-- **The base case of Gleason's theorem, in dimension one.**  Here no analytic input is needed:
the only subspaces are `⊥` and `⊤`, and every quantum measure is the one induced by the
identity operator. -/
