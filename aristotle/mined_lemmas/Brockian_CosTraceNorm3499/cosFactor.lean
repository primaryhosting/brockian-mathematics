import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Brockian

open Matrix

/-- The trace norm (Schatten `1`-norm) of a Hermitian complex matrix: the sum of the absolute
values of its eigenvalues.  (It is set to `0` on non-Hermitian matrices, which we never use.) -/

noncomputable def cosFactor {N m : ℕ} (c w : Fin m → ℝ) (x : Fin N → ℝ) :
    Matrix (Fin m × Fin 2) (Fin N) ℂ :=
  fun p j => ((Real.sqrt (c p.1) *
    (if p.2 = 0 then Real.cos (w p.1 * x j) else Real.sin (w p.1 * x j)) : ℝ) : ℂ)

