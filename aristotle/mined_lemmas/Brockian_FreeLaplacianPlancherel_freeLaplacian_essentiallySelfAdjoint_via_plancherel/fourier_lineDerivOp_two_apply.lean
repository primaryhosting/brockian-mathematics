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

lemma fourier_lineDerivOp_two_apply (f : 𝓢(E, ℂ)) (v ξ : E) :
    𝓕 (∂_{v} (∂_{v} f)) ξ = -(4 * π ^ 2 * (inner ℝ ξ v : ℝ) ^ 2) * 𝓕 f ξ := by
  have hgrow : Function.HasTemperateGrowth (fun x : E => (inner ℝ x v : ℝ)) :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
  simp only [SchwartzMap.smul_apply, smulLeftCLM_apply hgrow, Complex.real_smul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Plancherel's formula for the Laplacian**: the Fourier transform of `Δ f` is multiplication
by `-4π²‖ξ‖²`, i.e. by minus the symbol `laplacianSymbol`. -/
