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

theorem fourier_adjoint_apply
    (hfourier : ∀ φ : 𝓢(EuclSpace d, ℂ), 𝓕 (negLaplacianCLM d φ) = mulSymbolCLM d (𝓕 φ))
    (x : ((freeLaplacian d)†).domain) :
    (fun ξ ↦ ((symbol d ξ : ℝ) : ℂ) * (𝓕 (x : L2 d) : L2 d) ξ)
      =ᵐ[volume] ((𝓕 ((freeLaplacian d)† x) : L2 d) : EuclSpace d → ℂ) := by
  refine ae_symbol_mul_eq (𝓕 (x : L2 d)) (𝓕 ((freeLaplacian d)† x)) ?_
  intro ψ
  have hdense : Dense (((freeLaplacian d).domain : Submodule ℂ (L2 d)) : Set (L2 d)) :=
    dense_domain_freeLaplacian d
  set φ : 𝓢(EuclSpace d, ℂ) := 𝓕⁻ ψ
  have hφ : 𝓕 φ = ψ := FourierTransform.fourier_fourierInv_eq ψ
  have e1 : (ψ.toLp 2 (volume : Measure (EuclSpace d)) : L2 d)
      = 𝓕 (φ.toLp 2 (volume : Measure (EuclSpace d))) := by
    rw [SchwartzMap.toLp_fourier_eq, hφ]
  have e2 : ((mulSymbolCLM d ψ).toLp 2 (volume : Measure (EuclSpace d)) : L2 d)
      = 𝓕 ((negLaplacianCLM d φ).toLp 2 (volume : Measure (EuclSpace d))) := by
    rw [SchwartzMap.toLp_fourier_eq, hfourier φ, hφ]
  rw [e1, e2, MeasureTheory.Lp.inner_fourier_eq, MeasureTheory.Lp.inner_fourier_eq]
  have hFA := LinearPMap.adjoint_isFormalAdjoint (T := freeLaplacian d) hdense x
    ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩
  rw [hFA, freeLaplacian_apply_toLp]

