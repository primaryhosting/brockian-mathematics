import Brockian.Weyl.FreeLaplacian2

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

/-
Essential self-adjointness of the free Laplacian on `L²(ℝᵈ)`, via the Fourier transform.
-/
import Mathlib

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Function LineDeriv
open scoped FourierTransform ComplexInnerProductSpace Laplacian LinearPMap ContDiff

noncomputable section

variable (d : ℕ)

/-- The configuration space `ℝᵈ`. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝᵈ, ℂ)`. -/
abbrev L2 (d : ℕ) := Lp (α := EuclSpace d) ℂ 2

/-- The symbol of the free Laplacian: `-Δ` acts on the Fourier side as multiplication by
`4π²‖ξ‖²`. -/

theorem fourier_lineDerivOp_sq_apply (φ : 𝓢(EuclSpace d, ℂ)) (m x : EuclSpace d) :
    (𝓕 (∂_{m} (∂_{m} φ)) : 𝓢(EuclSpace d, ℂ)) x
      = -(4 * (π : ℂ) ^ 2 * ((inner ℝ x m : ℝ) : ℂ) ^ 2) * (𝓕 φ : 𝓢(EuclSpace d, ℂ)) x := by
  have hg : Function.HasTemperateGrowth (fun x : EuclSpace d ↦ (inner ℝ x m : ℝ)) :=
    Function.hasTemperateGrowth_inner_left m
  rw [SchwartzMap.fourier_lineDerivOp_eq, SchwartzMap.fourier_lineDerivOp_eq]
  simp only [SchwartzMap.smul_apply, smulLeftCLM_apply_apply hg, Complex.real_smul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

variable (d)

/-- The Fourier transform intertwines `-Δ` on Schwartz space with multiplication by the
symbol `4π²‖ξ‖²`. -/
