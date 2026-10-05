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

def multDomain (μ : Measure α) (m : α → ℝ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (fun x => (m x : ℂ) * ⇑f x) 2 μ}
  add_mem' := by
    intro u v hu hv
    have h : (fun x => (m x : ℂ) * ⇑(u + v) x)
        =ᵐ[μ] (fun x => (m x : ℂ) * ⇑u x) + (fun x => (m x : ℂ) * ⇑v x) := by
      filter_upwards [Lp.coeFn_add u v] with x hx
      rw [hx]
      simp [mul_add]
    exact (memLp_congr_ae h).2 (hu.add hv)
  zero_mem' := by
    have h : (fun x => (m x : ℂ) * ⇑(0 : Lp ℂ 2 μ) x) =ᵐ[μ] (0 : α → ℂ) := by
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx
      rw [hx]
      simp
    exact (memLp_congr_ae h).2 MemLp.zero
  smul_mem' := by
    intro c u hu
    have h : (fun x => (m x : ℂ) * ⇑(c • u) x) =ᵐ[μ] c • (fun x => (m x : ℂ) * ⇑u x) := by
      filter_upwards [Lp.coeFn_smul c u] with x hx
      rw [hx]
      simp [Pi.smul_apply]
      ring
    exact (memLp_congr_ae h).2 (hu.const_smul c)

