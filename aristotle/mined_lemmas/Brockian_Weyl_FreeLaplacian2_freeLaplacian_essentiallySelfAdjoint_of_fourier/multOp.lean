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

def multOp (μ : Measure α) (m : α → ℝ) : multDomain μ m →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := MemLp.toLp _ (mem_multDomain_iff.1 f.2)
  map_add' := by
    intro u v
    rw [Lp.ext_iff]
    filter_upwards [MemLp.coeFn_toLp (mem_multDomain_iff.1 (u + v).2),
      MemLp.coeFn_toLp (mem_multDomain_iff.1 u.2), MemLp.coeFn_toLp (mem_multDomain_iff.1 v.2),
      Lp.coeFn_add (MemLp.toLp _ (mem_multDomain_iff.1 u.2))
        (MemLp.toLp _ (mem_multDomain_iff.1 v.2)),
      Lp.coeFn_add (u : Lp ℂ 2 μ) (v : Lp ℂ 2 μ)] with x h1 h2 h3 h4 h5
    simp only [Submodule.coe_add, Pi.add_apply] at *
    rw [h1, h4, h2, h3, h5]
    ring
  map_smul' := by
    intro c u
    rw [Lp.ext_iff]
    filter_upwards [MemLp.coeFn_toLp (mem_multDomain_iff.1 (c • u).2),
      MemLp.coeFn_toLp (mem_multDomain_iff.1 u.2),
      Lp.coeFn_smul c (MemLp.toLp _ (mem_multDomain_iff.1 u.2)),
      Lp.coeFn_smul c (u : Lp ℂ 2 μ)] with x h1 h2 h3 h4
    simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul] at *
    rw [h1, h3, h2, h4]
    ring

