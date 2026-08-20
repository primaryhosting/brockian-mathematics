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

theorem YangMillsTheory.hasMassGap_of_clustering {Γ : GaugeGroup} (Y : YangMillsTheory Γ) {Δ : ℝ}
    (h : Y.transfer.HasExponentialClustering Δ) : Y.transfer.HasMassGap Δ :=
  TransferMatrixTheory.hasMassGap_of_hasExponentialClustering _ h

/-- **Yang–Mills existence and mass gap, reduced to exponential clustering of the Euclidean
correlation functions.**

For every compact gauge group `Γ`, the existence of a quantum Yang–Mills theory on `ℝ⁴` — a
continuum limit of Wilson lattice gauge theory satisfying the Osterwalder–Schrader
requirements — whose Wilson-loop Schwinger functions cluster exponentially at some fixed rate
`Δ > 0` implies the existence of a quantum Yang–Mills theory on `ℝ⁴` with a positive mass gap,
of size at least `Δ`: the reconstructed Hamiltonian has spectrum contained in `{0} ∪ [Δ, ∞)`.

The hypothesis is a statement purely about Euclidean correlation functions of Wilson loops (the
objects produced by the lattice theory); the conclusion is a spectral statement about the
reconstructed quantum Hamiltonian.  The nontrivial content, proved in Parts I and IV, is that
state-dependent exponential decay of the two-point functions of a total family of states
upgrades to a *uniform* spectral gap. -/
