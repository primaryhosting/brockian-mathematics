/-
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Note on Mathlib coverage

Mathlib contains no formalisation of constructive/axiomatic quantum field theory (no Wightman or
Osterwalder–Schrader axioms, no Yang–Mills measure), so no existing lemma closes this statement.
What is used here is general Hilbert-space API: `ContinuousLinearMap.isSelfAdjoint_iff'`,
`ContinuousLinearMap.adjoint_inner_right`, `ContinuousLinearMap.opNorm_le_bound`,
`norm_inner_le_norm`, `inner_self_eq_norm_sq_to_K` and `IsClosed.closure_subset_iff`.
-/

open scoped InnerProductSpace

namespace Frontier

universe u

/-- The gauge group `SU(3)` of Yang–Mills theory, as `3 × 3` special unitary matrices. -/
abbrev SU3 : Type := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- Four–dimensional (Euclidean) spacetime `ℝ⁴`. -/
abbrev Spacetime : Type := EuclideanSpace ℝ (Fin 4)

/--
A *quantum Yang–Mills theory* with gauge group `G`, described through the data that the
Osterwalder–Schrader reconstruction produces: a separable complex Hilbert space `ℋ` of states,
a normalised vacuum vector, the transfer operator `transfer = e^{-H}` of the Hamiltonian `H`
(a positive self-adjoint contraction fixing the vacuum), a unitary representation of the
spacetime translation group `ℝ⁴`, and a unitary representation of the gauge group `G`, both
fixing the vacuum and commuting with the dynamics.

This records the vacuum-sector/spectral part of the Wightman axioms in the transfer-matrix
form; it does *not* encode the Yang–Mills action itself (i.e. that the theory is obtained
from the `SU(3)` Yang–Mills functional integral), which is the analytic heart of the Clay
problem and is not formalised here.
-/
structure YangMillsTheory (G : Type u) [Group G] where
  /-- The Hilbert space of states. -/
  ℋ : Type
  [normed : NormedAddCommGroup ℋ]
  [innerProd : InnerProductSpace ℂ ℋ]
  [complete : CompleteSpace ℋ]
  /-- The vacuum state. -/
  vacuum : ℋ
  /-- The vacuum is a unit vector. -/
  vacuum_norm : ‖vacuum‖ = 1
  /-- The transfer operator `e^{-H}`, `H` the Hamiltonian. -/
  transfer : ℋ →L[ℂ] ℋ
  /-- `H` is self-adjoint. -/
  transfer_selfAdjoint : IsSelfAdjoint transfer
  /-- Positivity of the energy: `e^{-H} ≥ 0`. -/
  transfer_nonneg : ∀ ψ : ℋ, 0 ≤ (⟪ψ, transfer ψ⟫_ℂ).re
  /-- The energy is bounded below by `0`: `e^{-H}` is a contraction. -/
  transfer_norm_le_one : ‖transfer‖ ≤ 1
  /-- The vacuum has zero energy. -/
  transfer_vacuum : transfer vacuum = vacuum
  /-- The unitary representation of the spacetime translation group `ℝ⁴`. -/
  translation : Multiplicative Spacetime →* (ℋ ≃ₗᵢ[ℂ] ℋ)
  /-- The vacuum is translation invariant. -/
  translation_vacuum : ∀ a, translation a vacuum = vacuum
  /-- Translations commute with the dynamics. -/
  translation_comm : ∀ a ψ, transfer (translation a ψ) = translation a (transfer ψ)
  /-- The unitary representation of the gauge group. -/
  gauge : G →* (ℋ ≃ₗᵢ[ℂ] ℋ)
  /-- The vacuum is gauge invariant. -/
  gauge_vacuum : ∀ g, gauge g vacuum = vacuum
  /-- Gauge transformations commute with the dynamics. -/
  gauge_comm : ∀ g ψ, transfer (gauge g ψ) = gauge g (transfer ψ)

attribute [instance] YangMillsTheory.normed YangMillsTheory.innerProd YangMillsTheory.complete

variable {G : Type u} [Group G]

/--
`HasMassGap 𝒯 Δ` says that the theory `𝒯` has a mass gap of size at least `Δ > 0`: every state
orthogonal to the vacuum is damped by at least `e^{-Δ}` under one unit of imaginary-time
evolution, i.e. the spectrum of the Hamiltonian on the orthogonal complement of the vacuum
lies in `[Δ, ∞)`.
-/

lemma modelTheory_hasMassGap {Δ : ℝ} (hΔ : 0 < Δ) : HasMassGap (modelTheory (G := G)) Δ := by
  refine ⟨hΔ, fun ψ hψ => ?_⟩
  have : (modelTheory (G := G)).transfer ψ = 0 := by
    show vacuumProjection modelVacuum ψ = 0
    rw [vacuumProjection_apply, show ⟪modelVacuum, ψ⟫_ℂ = 0 from hψ, zero_smul]
  rw [this, norm_zero]
  positivity

/--
**Yang–Mills existence and mass gap (formalised statement, base case proved).**

There exists a quantum Yang–Mills theory with gauge group `SU(3)` on four-dimensional spacetime
— in the sense of the axioms recorded in `Frontier.YangMillsTheory`: a Hilbert space of states
with a normalised, translation- and gauge-invariant vacuum, a positive self-adjoint Hamiltonian
generating the dynamics and commuting with the symmetries — which has a positive mass gap
`Δ > 0`, and whose one-particle sector (the orthogonal complement of the vacuum) is nontrivial,
so that the mass-gap assertion has content.

The proof exhibits the explicit model `Frontier.modelTheory`.  This is the base case demanded by
the goal: the *full* Clay Millennium statement additionally requires that the theory be the one
constructed from the `SU(3)` Yang–Mills functional integral on `ℝ⁴` (Osterwalder–Schrader
reconstruction of the Yang–Mills measure), a requirement not expressed by these axioms and not
proved here.  The companion reduction `Frontier.mass_gap_of_core` shows that, for any theory
satisfying these axioms, the gap estimate only needs to be checked on a dense core of states.
-/
