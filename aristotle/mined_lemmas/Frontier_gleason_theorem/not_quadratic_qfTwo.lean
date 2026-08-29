import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A *frame function of weight one*, Gleason's formulation of a quantum measure:
a function on the unit sphere which is nonnegative and whose values sum to `1`
over every orthonormal basis. -/
structure IsFrameFunction (f : H → ℝ) : Prop where
  nonneg : ∀ x : H, ‖x‖ = 1 → 0 ≤ f x
  sum_eq_one : ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H, ∑ i, f (b i) = 1

/-- A density operator: a positive (hence self-adjoint) operator of trace one. -/

theorem not_quadratic_qfTwo :
    ¬ ∃ T : C2 →L[ℂ] C2, ∀ x : C2, ‖x‖ = 1 → ((qfTwo x : ℂ) = ⟪T x, x⟫_ℂ) := by
  rintro ⟨T, hT⟩
  set x₁ : C2 := !₂[(3 / 5 : ℂ), (4 / 5 : ℂ)] with hx₁
  set x₂ : C2 := !₂[(3 / 5 : ℂ), -(4 / 5 : ℂ)] with hx₂
  have hnx₁ : ‖x₁‖ = 1 := by rw [EuclideanSpace.norm_eq]; norm_num [hx₁, Fin.sum_univ_two]
  have hnx₂ : ‖x₂‖ = 1 := by rw [EuclideanSpace.norm_eq]; norm_num [hx₂, Fin.sum_univ_two]
  have hq₁ : qfTwo x₁ = 81 / 337 := by norm_num [qfTwo, hx₁]
  have hq₂ : qfTwo x₂ = 81 / 337 := by norm_num [qfTwo, hx₂]
  have hd₁ : x₁ = (3 / 5 : ℂ) • stdE0 + (4 / 5 : ℂ) • stdE1 := by
    ext i; fin_cases i <;> simp [hx₁, stdE0, stdE1]
  have hd₂ : x₂ = (3 / 5 : ℂ) • stdE0 - (4 / 5 : ℂ) • stdE1 := by
    ext i; fin_cases i <;> simp [hx₂, stdE0, stdE1]
  have expand : ⟪T x₁, x₁⟫_ℂ + ⟪T x₂, x₂⟫_ℂ
      = (18 / 25 : ℂ) * ⟪T stdE0, stdE0⟫_ℂ + (32 / 25 : ℂ) * ⟪T stdE1, stdE1⟫_ℂ := by
    rw [hd₁, hd₂]
    simp
    ring
  rw [← hT x₁ hnx₁, ← hT x₂ hnx₂, ← hT stdE0 norm_stdE0, ← hT stdE1 norm_stdE1,
    qfTwo_stdE0, qfTwo_stdE1, hq₁, hq₂] at expand
  norm_num at expand

/-- **Gleason's theorem fails in dimension two**: there is a quantum measure on `ℂ²`
which is not given by any density operator. -/
