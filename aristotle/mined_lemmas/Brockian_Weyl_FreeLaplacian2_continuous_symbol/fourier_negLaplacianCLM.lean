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

theorem fourier_negLaplacianCLM (φ : 𝓢(EuclSpace d, ℂ)) :
    𝓕 (negLaplacianCLM d φ) = mulSymbolCLM d (𝓕 φ) := by
  set b := stdOrthonormalBasis ℝ (EuclSpace d)
  have h1 : negLaplacianCLM d φ = -∑ i, ∂_{b i} (∂_{b i} φ) := by
    rw [negLaplacianCLM_apply, SchwartzMap.laplacian_eq_sum b φ]
  rw [h1, FourierTransform.fourier_neg, FourierTransform.fourier_sum]
  ext ξ
  simp only [SchwartzMap.neg_apply, SchwartzMap.sum_apply, mulSymbolCLM_apply,
    fourier_lineDerivOp_sq_apply]
  have hsum : ∑ i, ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2 = ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by
    have hb2 := OrthonormalBasis.sum_sq_inner_left b ξ
    have h2 : ((∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 : ℝ) : ℂ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by rw [hb2]
    push_cast at h2
    exact h2
  rw [symbol]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, neg_neg, ← Finset.sum_mul, ← Finset.mul_sum, hsum]

/-- The image of Schwartz space inside `L²(ℝᵈ)`; this is the domain of the free Laplacian. -/
