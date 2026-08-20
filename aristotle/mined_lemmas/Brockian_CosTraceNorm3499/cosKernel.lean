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

noncomputable def cosKernel {N m : ℕ} (c w : Fin m → ℝ) (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((∑ k, c k * Real.cos (w k * (x i - x j)) : ℝ) : ℂ)

/-- A rectangular factor `B` with `Bᴴ * B = cosKernel c w x` (for nonnegative weights). -/
