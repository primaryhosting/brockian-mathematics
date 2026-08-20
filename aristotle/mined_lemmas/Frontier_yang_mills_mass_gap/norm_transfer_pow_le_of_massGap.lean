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

theorem norm_transfer_pow_le_of_massGap (𝒯 : YangMillsTheory G) {Δ : ℝ} (h : HasMassGap 𝒯 Δ)
    (n : ℕ) (ψ : 𝒯.ℋ) (hψ : ⟪𝒯.vacuum, ψ⟫_ℂ = 0) :
    ‖(𝒯.transfer ^ n) ψ‖ ≤ Real.exp (-Δ * n) * ‖ψ‖ := by
  induction n generalizing ψ with
  | zero => simp
  | succ n ih =>
      have hstep : ‖(𝒯.transfer ^ n) (𝒯.transfer ψ)‖
          ≤ Real.exp (-Δ * n) * ‖𝒯.transfer ψ‖ := ih _ (transfer_mem_orthogonal 𝒯 hψ)
      have hT : ‖𝒯.transfer ψ‖ ≤ Real.exp (-Δ) * ‖ψ‖ := h.2 ψ hψ
      have hpow : ((𝒯.transfer ^ (n + 1)) ψ) = (𝒯.transfer ^ n) (𝒯.transfer ψ) := by
        rw [pow_succ]; rfl
      calc ‖(𝒯.transfer ^ (n + 1)) ψ‖ = ‖(𝒯.transfer ^ n) (𝒯.transfer ψ)‖ := by rw [hpow]
        _ ≤ Real.exp (-Δ * n) * ‖𝒯.transfer ψ‖ := hstep
        _ ≤ Real.exp (-Δ * n) * (Real.exp (-Δ) * ‖ψ‖) := by
              exact mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le
        _ = Real.exp (-Δ * ((n : ℝ) + 1)) * ‖ψ‖ := by
              rw [← mul_assoc, ← Real.exp_add]
              congr 2
              ring
        _ = Real.exp (-Δ * ((n + 1 : ℕ) : ℝ)) * ‖ψ‖ := by push_cast; ring_nf

/-!
### A model satisfying the axioms

We exhibit an explicit theory satisfying the above axioms with an arbitrarily large mass gap:
the rank-one transfer operator `ψ ↦ ⟪Ω, ψ⟫ • Ω` on a two-dimensional state space (a
"topological", infinitely massive theory).  This is the base case: the existence statement below
is therefore not vacuous, but it does *not* solve the Clay problem, which additionally demands
that the theory be the one constructed from the `SU(3)` Yang–Mills action on `ℝ⁴`.
-/

section Model

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The rank-one orthogonal projection onto the line spanned by `Ω`. -/
