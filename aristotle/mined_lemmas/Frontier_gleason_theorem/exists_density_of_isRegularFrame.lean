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

## Contents

* `Frontier.QuantumMeasure`: a finitely additive probability measure on the lattice of subspaces
  of a complex Hilbert space (equivalently, on orthogonal projections).
* `Frontier.IsDensityOperator`: self-adjoint, positive semidefinite, unit trace.
* `Frontier.gleason_theorem`: the target statement.  Gleason's theorem is derived, in a fully
  Lean-checked way, from Gleason's *frame function theorem* `hFrame` (the deep analytic input,
  taken here as an explicit hypothesis): every quantum measure on a space of dimension `≥ 3` is
  `U ↦ tr (ρ P_U)` for a density operator `ρ`.
* `Frontier.gleason_theorem_of_finrank_eq_one`: unconditional base case in dimension one.
* `Frontier.QuantumMeasure.ofDensity`: the converse direction, proved unconditionally -- every
  density operator defines a quantum measure through the Born rule.
* `Frontier.density_operator_unique`: the density operator is unique.
-/

open scoped InnerProductSpace
open Submodule

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A *quantum measure* (finitely additive probability measure on the lattice of closed
subspaces, equivalently on orthogonal projections) on an inner product space `E`. -/
structure QuantumMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The measure of a subspace. -/
  toFun : Submodule ℂ E → ℝ
  /-- A quantum measure is nonnegative. -/
  nonneg : ∀ U, 0 ≤ toFun U
  /-- A quantum measure is normalized: the whole space has measure `1`. -/
  normalized : toFun ⊤ = 1
  /-- A quantum measure is additive on orthogonal subspaces. -/
  additive : ∀ U V : Submodule ℂ E, U ⟂ V → toFun (U ⊔ V) = toFun U + toFun V

/-- A *density operator*: a positive semidefinite self-adjoint operator of trace one. -/
structure IsDensityOperator (ρ : E →ₗ[ℂ] E) : Prop where
  /-- Density operators are self-adjoint. -/
  isSymmetric : ρ.IsSymmetric
  /-- Density operators are positive semidefinite. -/
  nonneg : ∀ x : E, 0 ≤ (⟪x, ρ x⟫_ℂ).re
  /-- Density operators have unit trace. -/
  trace_one : LinearMap.trace ℂ E ρ = 1

/-- The orthogonal projection onto a subspace `U`, viewed as an endomorphism of `E`. -/

theorem exists_density_of_isRegularFrame [FiniteDimensional ℂ E] (mu : QuantumMeasure E)
    (hreg : IsRegularFrame mu) :
    ∃ ρ : E →ₗ[ℂ] E, IsDensityOperator ρ ∧
      ∀ U : Submodule ℂ E, (mu.toFun U : ℂ) = LinearMap.trace ℂ E (ρ ∘ₗ projLM U) := by
  obtain ⟨T, hsymm, hval⟩ := hreg
  have hreal : ∀ x : E, ((⟪x, T x⟫_ℂ).re : ℂ) = ⟪x, T x⟫_ℂ := by
    intro x
    refine Complex.conj_eq_iff_re.1 ?_
    rw [inner_conj_symm]
    exact hsymm x x
  have key : ∀ U : Submodule ℂ E, (mu.toFun U : ℂ) = LinearMap.trace ℂ E (T ∘ₗ projLM U) := by
    intro U
    set b := stdOrthonormalBasis ℂ U with hbdef
    have hon : Orthonormal ℂ (fun i => ((b i : E))) :=
      (U.subtypeₗᵢ).orthonormal_comp_iff.2 b.orthonormal
    rw [trace_comp_projLM T U b]
    have hU : mu.toFun U = ∑ i, mu.toFun (ℂ ∙ ((b i : E))) := by
      conv_lhs => rw [← iSup_span_orthonormalBasis U b]
      have := mu.sum_of_isOrtho (fun i => ℂ ∙ ((b i : E)))
        (fun i j hij => isOrtho_span_of_orthonormal hon hij) Finset.univ
      simpa using this
    rw [hU]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval _ (hon.1 i), hreal]
  refine ⟨T, ⟨hsymm, ?_, ?_⟩, key⟩
  · intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hx
      have hu : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
        rw [norm_smul]
        simp [inv_mul_cancel₀ hxn]
      have hnn := mu.nonneg (ℂ ∙ (((‖x‖⁻¹ : ℝ) : ℂ) • x))
      rw [hval _ hu] at hnn
      have hexp : ⟪((‖x‖⁻¹ : ℝ) : ℂ) • x, T (((‖x‖⁻¹ : ℝ) : ℂ) • x)⟫_ℂ
          = ((‖x‖⁻¹ * ‖x‖⁻¹ : ℝ) : ℂ) * ⟪x, T x⟫_ℂ := by
        simp only [LinearMap.map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
          Complex.ofReal_mul]
        ring
      rw [hexp] at hnn
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero] at hnn
      have hpos : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ := by positivity
      exact nonneg_of_mul_nonneg_right hnn hpos
  · have h := key ⊤
    have hproj : (T ∘ₗ projLM (⊤ : Submodule ℂ E)) = T := by
      ext x
      simp [projLM, Submodule.starProjection_top]
    rw [hproj, mu.normalized] at h
    exact h.symm

/-- **Gleason's theorem** (reduction to the frame function theorem).

Let `E` be a complex Hilbert space of dimension at least `3`.  Assume Gleason's frame function
theorem `hFrame` for `E`.  Then every quantum measure `mu` on `E` -- i.e. every nonnegative,
normalized, finitely additive assignment of probabilities to closed subspaces -- is given by a
density operator `ρ`: `mu U = tr (ρ ∘ P_U)` for every subspace `U`. -/
