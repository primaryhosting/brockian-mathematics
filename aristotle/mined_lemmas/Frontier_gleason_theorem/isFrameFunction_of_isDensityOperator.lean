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

theorem isFrameFunction_of_isDensityOperator {T : H →L[ℂ] H} (hT : IsDensityOperator T) :
    IsFrameFunction (fun x : H => RCLike.re ⟪T x, x⟫_ℂ) where
  nonneg := fun x _ => hT.1.2 x
  sum_eq_one := by
    intro b
    rw [Finset.sum_congr rfl (fun i _ => re_inner_apply_self_symm T (b i)), ← Complex.re_sum]
    have hsum : ∑ i, ⟪b i, T (b i)⟫_ℂ = 1 := by
      rw [← hT.2, LinearMap.trace_eq_sum_inner (T : H →ₗ[ℂ] H) b]
      simp
    rw [hsum]
    norm_num

/-- **Gleason's theorem** (Lean-checked reduction).

Every quantum measure (frame function of weight one) on a complex Hilbert space of
dimension at least `3` is given by a density operator.

The analytic core of Gleason's argument is the statement that such a measure is
*quadratic*, i.e. of the form `x ↦ ⟪T x, x⟫` for some bounded operator `T`; that is taken
here as the hypothesis `hquad`, and what is proved is the reduction: once the measure is
quadratic, the operator representing it is automatically a density operator, i.e. positive
(hence self-adjoint) and of trace one.  The dimension hypothesis `hdim` is retained as part
of the statement, although this reduction step does not use it (it is needed only for the
quadraticity of the measure, which fails in dimension two).  The Hilbert space is assumed
finite dimensional. -/
