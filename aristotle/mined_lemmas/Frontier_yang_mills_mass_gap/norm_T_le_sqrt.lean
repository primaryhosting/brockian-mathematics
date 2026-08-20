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

lemma norm_T_le_sqrt (ψ : H) {C Δ : ℝ}
    (hC : ∀ t : ℝ, 0 ≤ t → ‖⟪ψ, Th.T t ψ⟫_ℂ‖ ≤ C * Real.exp (-Δ * t))
    {u : ℝ} (hu : 0 ≤ u) :
    ‖Th.T u ψ‖ ≤ Real.sqrt C * Real.exp (-Δ * u) := by
  have h1 : ‖Th.T u ψ‖ ^ 2 ≤ ‖⟪ψ, Th.T (2 * u) ψ⟫_ℂ‖ := by
    rw [norm_T_sq ψ hu]; exact Complex.re_le_norm _
  have h2 := hC (2 * u) (by linarith)
  have h3 : (Real.exp (-Δ * u)) ^ 2 = Real.exp (-Δ * (2 * u)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hbound : ‖Th.T u ψ‖ ^ 2 ≤ C * (Real.exp (-Δ * u)) ^ 2 := by
    rw [h3]; linarith
  have hCnn : 0 ≤ C := by
    by_contra hneg
    push_neg at hneg
    have he : (0:ℝ) < (Real.exp (-Δ * u)) ^ 2 := by positivity
    nlinarith [sq_nonneg ‖Th.T u ψ‖]
  calc ‖Th.T u ψ‖ = Real.sqrt (‖Th.T u ψ‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (C * (Real.exp (-Δ * u)) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt C * Real.exp (-Δ * u) := by
        rw [Real.sqrt_mul hCnn, Real.sqrt_sq (Real.exp_pos _).le]

/-- **Key estimate.** For a state with exponentially decaying two-point function, the
decay is in fact uniform: `‖T s ψ‖ ≤ e^{-Δ s} ‖ψ‖`, with no state-dependent constant. -/
