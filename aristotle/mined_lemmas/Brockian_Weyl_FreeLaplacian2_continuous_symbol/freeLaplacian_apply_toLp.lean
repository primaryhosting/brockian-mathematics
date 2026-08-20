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

theorem freeLaplacian_apply_toLp (φ : 𝓢(EuclSpace d, ℂ)) :
    (freeLaplacian d) ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩ =
      (negLaplacianCLM d φ).toLp 2 volume := by
  have h : (schwartzEquiv d).symm ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩ = φ := by
    apply (schwartzEquiv d).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  show ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d)))
      ((negLaplacianCLM d) ((schwartzEquiv d).symm ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩))) = _
  rw [h]
  rfl

/-- Every element of the domain of the free Laplacian comes from a Schwartz function. -/
