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

theorem trace_eq_one_of_frameFunction [FiniteDimensional ℂ H] {f : H → ℝ}
    (hf : IsFrameFunction f) {T : H →L[ℂ] H}
    (hT : ∀ x : H, ‖x‖ = 1 → ((f x : ℂ) = ⟪T x, x⟫_ℂ)) :
    LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) = 1 := by
  set b := stdOrthonormalBasis ℂ H with hb
  rw [LinearMap.trace_eq_sum_inner (T : H →ₗ[ℂ] H) b]
  simp only [ContinuousLinearMap.coe_coe]
  have key : ∀ i, ⟪b i, T (b i)⟫_ℂ = ((f (b i) : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm, ← hT (b i) (b.norm_eq_one i)]
    simp
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Complex.ofReal_sum, hf.sum_eq_one b]
  norm_num

/-- The quantum measure attached to a density operator is a frame function of weight one:
the converse direction of Gleason's theorem. -/
