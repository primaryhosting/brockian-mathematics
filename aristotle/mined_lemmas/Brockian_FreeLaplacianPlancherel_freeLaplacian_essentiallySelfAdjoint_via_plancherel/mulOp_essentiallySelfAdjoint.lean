import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex
open scoped Real ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ## Essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely defined symmetric operator `T` with domain `D` in a complex Hilbert space is
*essentially self-adjoint* when both deficiency spaces are trivial, i.e. when the ranges of
`T + i` and `T - i` are dense. -/

theorem mulOp_essentiallySelfAdjoint :
    IsEssentiallySelfAdjoint (mulDomain m hm μ) (mulOp m hm μ) := by
  refine ⟨mulDomain_dense m hm μ, mulOp_symmetric m hm μ, ?_, ?_⟩
  · exact mulOp_dense_range m hm μ Complex.I (by simp) (by simp)
  · have h := mulOp_dense_range m hm μ (-Complex.I) (by simp) (by simp)
    simpa [sub_eq_add_neg] using h

end Multiplication

/-! ## The free Laplacian -/

section FreeLaplacian

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Fourier symbol of the free Laplacian `-Δ`: `4π²‖ξ‖²`. -/
