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

theorem hasMassGap_of_total_clustering {Δ : ℝ} (hΔ : 0 < Δ) (S : Set H)
    (hSdense : Dense ((Submodule.span ℂ S : Submodule ℂ H) : Set H))
    (hS : ∀ x ∈ S, Th.vacuumComplProj x ∈ Th.clusterSubspace Δ) :
    Th.HasMassGap Δ := by
  refine hasMassGap_of_dense_clusterSubspace Th hΔ fun ψ hψ => ?_
  have hspan : Submodule.span ℂ S ≤ (Th.clusterSubspace Δ).comap (Th.vacuumComplProj : H →ₗ[ℂ] H) := by
    refine Submodule.span_le.2 fun x hx => ?_
    simpa [Submodule.mem_comap] using hS x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, hvmem, hv⟩ := Metric.mem_closure_iff.1 (hSdense.closure_eq ▸ Set.mem_univ ψ) (ε / 3)
    (by linarith)
  refine ⟨Th.vacuumComplProj v, hspan hvmem, ?_⟩
  have hproj : ψ - Th.vacuumComplProj v = Th.vacuumComplProj (ψ - v) := by
    rw [map_sub, Th.vacuumComplProj_of_orthogonal hψ]
  have : dist ψ (Th.vacuumComplProj v) ≤ 2 * dist ψ v := by
    rw [dist_eq_norm, dist_eq_norm, hproj]
    exact Th.norm_vacuumComplProj_le _
  linarith

end Density

end TransferMatrixTheory

/-! ## Part I.b  Consistency: the axioms are satisfiable, with a genuine gap

The axioms of `TransferMatrixTheory`, of `HasExponentialClustering` and of `HasMassGap` are not
vacuous.  For any unit vector `Ω` in any complex Hilbert space, the semigroup
`T t = e^{-t}(1 - P_Ω) + P_Ω` (a single massive mode of mass one above the vacuum) satisfies all
of them, with gap `Δ = 1`. -/

section GappedModel

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `vacuumMix Ω a = a • id + (1 - a) • P_Ω`, where `P_Ω` is the rank-one projection on `Ω`. -/
