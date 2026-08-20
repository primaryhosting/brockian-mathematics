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

theorem dense_compactSupport_toL2 :
    Dense {x : L2Space V | ∃ ψ : 𝓢(V, ℂ), HasCompactSupport ψ ∧ toL2 V ψ = x} := by
  have hd := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (E := V) (F := ℂ) (μ := volume)
    (p := 2) ENNReal.ofNat_ne_top
  refine hd.mono ?_
  rintro x ⟨g, hxg, hcs, hcd⟩
  refine ⟨hcs.toSchwartzMap hcd, by simpa using hcs, ?_⟩
  refine Lp.ext_iff.mpr ?_
  filter_upwards [(hcs.toSchwartzMap hcd).coeFn_toLp 2 (volume : Measure V), hxg] with y hy hy2
  rw [toL2_apply, hy, hy2]
  simp

