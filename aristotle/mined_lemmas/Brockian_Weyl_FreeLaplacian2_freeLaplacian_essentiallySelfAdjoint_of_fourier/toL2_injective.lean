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
# The basic criterion for essential self-adjointness

This file develops the abstract operator-theoretic input for `Brockian.Weyl.FreeLaplacian2`:
a densely defined symmetric operator on a complex Hilbert space whose two deficiency ranges
`Ran (T + i)` and `Ran (T - i)` are dense has self-adjoint closure, i.e. it is
*essentially self-adjoint*.
-/

namespace Brockian.Weyl

open LinearPMap Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `x ↦ T x + z • x` on the domain of `T`. -/

theorem toL2_injective : Function.Injective (toL2 V) := by
  intro f g h
  have h1 : (f : V → ℂ) =ᵐ[volume] (g : V → ℂ) := by
    filter_upwards [f.coeFn_toLp 2 (volume : Measure V), g.coeFn_toLp 2 (volume : Measure V)]
      with x hx hy
    rw [← hx, ← hy]
    exact congrFun (congrArg (fun u : L2Space V => (u : V → ℂ)) h) x
  exact SchwartzMap.ext
    (congrFun ((Continuous.ae_eq_iff_eq volume f.continuous g.continuous).mp h1))

