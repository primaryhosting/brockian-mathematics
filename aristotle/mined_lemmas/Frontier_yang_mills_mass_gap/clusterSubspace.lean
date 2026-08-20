import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Part I. Transfer matrices, mass gap, and exponential clustering -/

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The kinematical data extracted from a Euclidean quantum field theory by the
Osterwalder–Schrader reconstruction: a (complex) Hilbert space of physical states, a
normalised vacuum vector, and the self-adjoint contraction semigroup `T t = e^{-tH}`
of Euclidean time translations, which fixes the vacuum. -/
structure TransferMatrixTheory (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The Euclidean time evolution semigroup `T t = e^{-t H}`. -/
  T : ℝ → (H →L[ℂ] H)
  /-- The vacuum state. -/
  vacuum : H
  norm_vacuum : ‖vacuum‖ = 1
  T_zero : T 0 = ContinuousLinearMap.id ℂ H
  T_add : ∀ ⦃s t : ℝ⦄, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)
  T_selfAdjoint : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x y : H, ⟪T t x, y⟫_ℂ = ⟪x, T t y⟫_ℂ
  T_contraction : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x : H, ‖T t x‖ ≤ ‖x‖
  T_vacuum : ∀ ⦃t : ℝ⦄, 0 ≤ t → T t vacuum = vacuum

namespace TransferMatrixTheory

variable (Th : TransferMatrixTheory H)

/-- The theory has a mass gap at least `Δ > 0`: on the orthogonal complement of the vacuum
the Euclidean evolution decays at least like `e^{-Δ t}`, uniformly in the state.  Equivalently,
the Hamiltonian has spectrum contained in `{0} ∪ [Δ, ∞)`. -/

noncomputable def clusterSubspace (Δ : ℝ) : Submodule ℂ H where
  carrier := {ψ : H | ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖⟪ψ, Th.T t ψ⟫_ℂ‖ ≤ C * Real.exp (-Δ * t)}
  zero_mem' := ⟨0, by intro t _; simp⟩
  add_mem' := by
    rintro ψ ψ₂ ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩
    refine ⟨‖ψ + ψ₂‖ * (‖ψ‖ + ‖ψ₂‖), fun t ht => ?_⟩
    have hψ : ‖Th.T t ψ‖ ≤ Real.exp (-Δ * t) * ‖ψ‖ := norm_T_le_of_clustering ψ hC₁ ht
    have hψ₂ : ‖Th.T t ψ₂‖ ≤ Real.exp (-Δ * t) * ‖ψ₂‖ := norm_T_le_of_clustering ψ₂ hC₂ ht
    have hsplit : ⟪ψ + ψ₂, Th.T t (ψ + ψ₂)⟫_ℂ
        = ⟪ψ + ψ₂, Th.T t ψ⟫_ℂ + ⟪ψ + ψ₂, Th.T t ψ₂⟫_ℂ := by
      rw [map_add, inner_add_right]
    calc ‖⟪ψ + ψ₂, Th.T t (ψ + ψ₂)⟫_ℂ‖
        ≤ ‖⟪ψ + ψ₂, Th.T t ψ⟫_ℂ‖ + ‖⟪ψ + ψ₂, Th.T t ψ₂⟫_ℂ‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ ‖ψ + ψ₂‖ * ‖Th.T t ψ‖ + ‖ψ + ψ₂‖ * ‖Th.T t ψ₂‖ := by
          gcongr <;> exact norm_inner_le_norm _ _
      _ ≤ ‖ψ + ψ₂‖ * (Real.exp (-Δ * t) * ‖ψ‖) + ‖ψ + ψ₂‖ * (Real.exp (-Δ * t) * ‖ψ₂‖) := by
          gcongr
      _ = ‖ψ + ψ₂‖ * (‖ψ‖ + ‖ψ₂‖) * Real.exp (-Δ * t) := by ring
  smul_mem' := by
    rintro a ψ ⟨C, hC⟩
    refine ⟨‖a‖ ^ 2 * C, fun t ht => ?_⟩
    have : ⟪a • ψ, Th.T t (a • ψ)⟫_ℂ = (starRingEnd ℂ) a * a * ⟪ψ, Th.T t ψ⟫_ℂ := by
      rw [map_smul, inner_smul_left, inner_smul_right]; ring
    rw [this, norm_mul, norm_mul, RCLike.norm_conj]
    have h1 := hC t ht
    nlinarith [norm_nonneg a, norm_nonneg (⟪ψ, Th.T t ψ⟫_ℂ), Real.exp_pos (-Δ * t)]

