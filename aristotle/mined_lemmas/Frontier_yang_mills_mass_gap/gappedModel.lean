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

noncomputable def gappedModel (Ω : H) (hΩ : ‖Ω‖ = 1) : TransferMatrixTheory H where
  T t := vacuumMix Ω (Real.exp (-t))
  vacuum := Ω
  norm_vacuum := hΩ
  T_zero := by
    ext x
    simp [vacuumMix_apply]
  T_add := by
    intro s t _ _
    rw [vacuumMix_comp Ω hΩ, ← Real.exp_add]
    ring_nf
  T_selfAdjoint := by
    intro t _ x y
    exact vacuumMix_selfAdjoint Ω _ x y
  T_contraction := by
    intro t ht x
    refine vacuumMix_norm_le Ω hΩ (Real.exp_pos _).le ?_ x
    rw [Real.exp_le_one_iff]
    linarith
  T_vacuum := by
    intro t _
    exact vacuumMix_vacuum Ω hΩ _

/-- The model clusters exponentially with rate `1`. -/
