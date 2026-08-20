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

lemma inner_vacuumComplProj_wilson (γ : ContinuumLoop) (hγ : γ.IsTimeZero) {t : ℝ} (ht : 0 ≤ t) :
    ⟪Y.transfer.vacuumComplProj (Y.wilson γ Y.transfer.vacuum),
        Y.transfer.T t (Y.transfer.vacuumComplProj (Y.wilson γ Y.transfer.vacuum))⟫_ℂ
      = Y.schwinger [γ.reflect, γ.timeShift t]
        - Y.schwinger [γ] * (starRingEnd ℂ) (Y.schwinger [γ]) := by
  set Th := Y.transfer
  set u : Y.space.carrier := Y.wilson γ Th.vacuum
  set c : ℂ := ⟪Th.vacuum, u⟫_ℂ with hc
  have hcS : c = Y.schwinger [γ] := Y.vacuum_expectation γ
  have hΩ1 : ⟪Th.vacuum, Th.vacuum⟫_ℂ = 1 := Th.inner_vacuum_self
  have hTΩ : Th.T t Th.vacuum = Th.vacuum := Th.T_vacuum ht
  have hproj : Th.vacuumComplProj u = u - c • Th.vacuum := rfl
  have hTproj : Th.T t (u - c • Th.vacuum) = Th.T t u - c • Th.vacuum := by
    rw [map_sub, map_smul, hTΩ]
  have huΩ : ⟪u, Th.vacuum⟫_ℂ = (starRingEnd ℂ) c := by
    rw [hc, ← inner_conj_symm]
  have hΩTu : ⟪Th.vacuum, Th.T t u⟫_ℂ = c := by
    rw [← Th.T_selfAdjoint ht, hTΩ]
  have hrec : ⟪u, Th.T t u⟫_ℂ = Y.schwinger [γ.reflect, γ.timeShift t] :=
    Y.reconstruction γ γ hγ hγ t ht
  rw [hproj, hTproj]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hΩ1, huΩ,
    hΩTu, hrec, hcS.symm]
  ring

/-- **Main reduction, at the level of a single theory.** A quantum Yang–Mills theory whose
Schwinger functions cluster exponentially at rate `Δ > 0` has a mass gap of size at least
`Δ`: the Hamiltonian obtained by Osterwalder–Schrader reconstruction has spectrum contained
in `{0} ∪ [Δ, ∞)`. -/
