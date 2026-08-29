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
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex ComplexInnerProductSpace FourierTransform

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## Essential self-adjointness -/

/-- A (densely defined) operator `T` with domain `D` inside a complex inner product space `H`
is *essentially self-adjoint* when it is densely defined, symmetric, and the ranges of
`T + i` and `T - i` are dense (the basic criterion for essential self-adjointness of a
symmetric operator). -/

lemma multOp_add_surjective (m : α → ℝ) (hm : Measurable m) (s : ℝ) (hs : s ≠ 0)
    (g : Lp ℂ 2 μ) :
    ∃ f : multDomain μ m, multOp μ m f + ((s : ℂ) * Complex.I) • (f : Lp ℂ 2 μ) = g := by
  obtain ⟨f, hf⟩ := exists_mem_multDomain_div m hm s hs g
  have hdne : ∀ x : α, (m x : ℂ) + (s : ℂ) * Complex.I ≠ 0 := by
    intro x hx
    apply hs
    have him : ((m x : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
    rw [← him, hx, Complex.zero_im]
  refine ⟨f, ?_⟩
  rw [Lp.ext_iff]
  filter_upwards [Lp.coeFn_add (multOp μ m f) (((s : ℂ) * Complex.I) • (f : Lp ℂ 2 μ)),
    multOp_coeFn m f, Lp.coeFn_smul ((s : ℂ) * Complex.I) (f : Lp ℂ 2 μ), hf] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul, h4]
  field_simp [hdne x]

/-- The maximal domain of a multiplication operator is dense. -/
