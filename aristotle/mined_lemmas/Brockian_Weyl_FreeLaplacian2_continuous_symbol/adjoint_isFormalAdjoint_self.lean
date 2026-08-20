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

theorem adjoint_isFormalAdjoint_self
    (hfourier : ∀ φ : 𝓢(EuclSpace d, ℂ), 𝓕 (negLaplacianCLM d φ) = mulSymbolCLM d (𝓕 φ)) :
    ((freeLaplacian d)†).IsFormalAdjoint ((freeLaplacian d)†) := by
  intro x y
  have hx := fourier_adjoint_apply hfourier x
  have hy := fourier_adjoint_apply hfourier y
  rw [← MeasureTheory.Lp.inner_fourier_eq ((freeLaplacian d)† x) (y : L2 d),
    ← MeasureTheory.Lp.inner_fourier_eq (x : L2 d) ((freeLaplacian d)† y),
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hx, hy] with ξ hxξ hyξ
  rw [← hxξ, ← hyξ]
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-! ### Essential self-adjointness -/

variable (d)

/-- **The free Laplacian is essentially self-adjoint.**  Conditional version: assuming the
Fourier transform intertwines `-Δ` with multiplication by the symbol `4π²‖ξ‖²` on Schwartz
space, the adjoint of the free Laplacian (with Schwartz domain) is self-adjoint, i.e. the free
Laplacian is essentially self-adjoint. -/
